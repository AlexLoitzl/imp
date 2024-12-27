Require Import imp.
Require Import Coq.Init.Nat.
Require Import Classes.EquivDec.
Require Import Coq.Arith.Wf_nat.
Require Import Psatz.

Axiom strong_induction:
forall P : nat -> Prop,
(forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
forall n : nat, P n.

Notation State := (Var -> nat).

(* Semantics of expressions, which we use for both small and big-step semantics *)
Fixpoint eval_Aexp (a : Aexp) (s : State) : nat :=
  match a with
  | NumE n => n
  | VarE v => s v
  | Plus a1 a2 => eval_Aexp a1 s + eval_Aexp a2 s
  | Minus a1 a2 => eval_Aexp a1 s - eval_Aexp a2 s
  | Times a1 a2 => eval_Aexp a1 s * eval_Aexp a2 s
  end.

Fixpoint eval_Bexp (b : Bexp) (s : State) : bool :=
  match b with
  | TrueE => true
  | FalseE => false
  | LE a1 a2 => (eval_Aexp a1 s) <=? (eval_Aexp a2 s)
  | Neg b => negb (eval_Bexp b s)
  | And b1 b2 => (eval_Bexp b1 s) && (eval_Bexp b2 s)
  | Or b1 b2 => (eval_Bexp b1 s) || (eval_Bexp b2 s)
  end.

(* Small-step semantics *)
(* We index the steps with associated costs *)

Inductive small_step `{EqDec Var} : nat -> (Prog * State) -> (Prog * State) -> Prop :=
| Sskip (s : State) : small_step 1 (skip, s) (skip, s)
| Sass (s : State) (v : Var) (a : Aexp) :
    small_step 1 (ass v a, s) (skip, fun x => if x == v then (eval_Aexp a s) else s x)
| SseqSkip (s1 s2 : State) (c1 c2 : Prog) (n : nat) (h : small_step n (c1, s1) (skip, s2)) :
    small_step (1 + n) (seq c1 c2, s1) (c2, s2)
| Sseq (s1 s2 : State) (c1 c1' c2 : Prog) (n : nat) (h : small_step n (c1, s1) (c1', s2)) (h' : c1' <> skip) :
    small_step (1 + n)(seq c1 c2, s1) (seq c1' c2, s2)
| SiteT (s : State) (b : Bexp) (c1 c2 : Prog) (hb : eval_Bexp b s = true) :
    small_step 1 (ite b c1 c2, s) (c1, s)
| SiteF (s : State) (b : Bexp) (c1 c2 : Prog) (hb : eval_Bexp b s = false) :
    small_step 1 (ite b c1 c2, s) (c2, s)
| SwhileT (s : State) (b : Bexp) (c : Prog) (hb : eval_Bexp b s = true) :
    small_step 1 (while b c, s) (seq c (while b c), s)
| SwhileF (s : State) (b : Bexp) (c : Prog) (hb : eval_Bexp b s = false) :
    small_step 1 (while b c, s) (skip, s).

(* Big-step semantics *)

(* We define semantics as a relation as we cannot encode unbounded loops *)
(* Inductive big_step  *)
Inductive big_step `{EqDec Var} : Prog -> State -> State -> Prop :=
| Bskip (s : State) : big_step skip s s
| Bass (s : State) (v : Var) (a : Aexp) :
    big_step (ass v a) s (fun x => if x == v then (eval_Aexp a s) else s x)
| Bseq (s1 s2 s3 : State) (c1 c2 : Prog) (h1 : big_step c1 s1 s2) (h2 : big_step c2 s2 s3) :
    big_step (seq c1 c2) s1 s3
| BiteT (s1 s2 : State) (b : Bexp) (c1 c2 : Prog) (hb : eval_Bexp b s1 = true)
    (h : big_step c1 s1 s2) : big_step (ite b c1 c2) s1 s2
| BiteF (s1 s2 : State) (b : Bexp) (c1 c2 : Prog) (hb : eval_Bexp b s1 = false)
    (h : big_step c2 s1 s2) : big_step (ite b c1 c2) s1 s2
| BwhileT (s1 s2 s3 : State) (b : Bexp) (c : Prog) (hb : eval_Bexp b s1 = true)
    (h1 : big_step c s1 s2) (h2 : big_step (while b c) s2 s3) : big_step (while b c) s1 s3
| BwhileF (s : State) (b : Bexp) (c : Prog) (hb : eval_Bexp b s = false) : big_step (while b c) s s.

Inductive refl_trans `{EqDec Var} : nat  -> (Prog * State) -> (Prog * State) -> Prop :=
| Refl (s : State) (c : Prog) : refl_trans 0 (c, s) (c, s)
| Trans (s1 s2 s3 : State) (c1 c2 c3 : Prog) (n1 n2 : nat) (h1 : small_step n1 (c1, s1) (c2, s2))
    (h2 : refl_trans n2 (c2, s2) (c3, s3)) : refl_trans (n1 + n2) (c1, s1) (c3, s3).

Lemma seq_split `{EqDec Var} :
  forall n c1 c2 s1 s3,
  refl_trans n (seq c1 c2, s1) (skip, s3) ->
  exists n1 n2 s2, refl_trans n1 (c1, s1) (skip, s2)
            /\ refl_trans n2 (c2, s2) (skip, s3)
            /\ n1 < n
            /\ n2 < n.
Proof.
  induction n using strong_induction; intros. inversion H1.
  - inversion h1.
    + exists (n0 + 0), n2, s2.
      repeat split; try lia.
      * econstructor. exact h. constructor.
      * exact h2.
    + rewrite <-H12 in h2.
      assert (hn2 : n2 <  n) by lia.
      destruct (H0 n2 hn2 _ _ _ _ h2) as (m1 & m2 & s' & Hl & Hr & Hm1 & Hm2).
      exists (n0 + m1), m2, s'.
      repeat split; try lia.
      * econstructor. exact h. exact Hl.
      * exact Hr.
Qed.

Lemma multi_skip `{EqDec Var} : forall n s1 s2, refl_trans n (skip, s1) (skip, s2) -> s1 = s2.
Proof.
  induction n; intros; inversion H0.
  - reflexivity.
  - destruct n1. inversion h1. discriminate.
  - inversion h1. rewrite <-H1 in H2. inversion H2. rewrite H11, <-H9 in h2.
    apply IHn. exact h2.
Qed.

Lemma imp_small_to_big `{EqDec Var} : forall n c s1 s2, refl_trans n (c, s1) (skip, s2) -> big_step c s1 s2.
Proof.
  induction n using strong_induction; intros; inversion H1.
  - constructor.
  - inversion h1.
    + eapply (H0 n2). lia. rewrite <-H11 in h2. exact h2.
    + rewrite <-H11 in h2. rewrite <-(multi_skip _ _ _ h2), <-H12. constructor.
    + rewrite <-H9 in H1. destruct (seq_split _ _ _ _ _ H1) as (m1 & m2 & s' & Hl & Hr & Hm1 & Hm2).
      econstructor.
      eapply (H0 _ Hm1). exact Hl.
      eapply (H0 _ Hm2). rewrite <-H11. exact Hr.
    + rewrite <-H9 in H1. destruct (seq_split _ _ _ _ _ H1) as (m1 & m2 & s' & Hl & Hr & Hm1 & Hm2).
      econstructor.
      eapply (H0 _ Hm1). exact Hl.
      eapply (H0 _ Hm2). exact Hr.
    + constructor. exact hb. eapply (H0 n2). lia. exact h2.
    + apply BiteF. exact hb. eapply (H0 n2). lia. exact h2.
    + rewrite <-H11 in h2.
      destruct (seq_split _ _ _ _ _ h2) as (m1 & m2 & s' & Hl & Hr & Hm1 & Hm2).
      eapply BwhileT. exact hb.
      eapply (H0 m1). lia. exact Hl.
      eapply (H0 m2). lia. exact Hr.
    + rewrite <-H11 in h2. rewrite <-(multi_skip _ _ _ h2). constructor. exact hb.
Qed.

Lemma skip_decidable : forall c, c = skip \/ c <> skip.
Proof.
  intro. destruct c; try (right; discriminate).
  tauto.
Qed.

Lemma seq_trans `{EqDec Var} :
  forall n1 n2 c1 c2 s1 s2 s3,
  refl_trans n1 (c1, s1) (skip, s2) ->
  refl_trans n2 (c2, s2) (skip, s3) ->
  exists n, refl_trans n (seq c1 c2, s1) (skip, s3).
Proof.
  induction n1 using strong_induction; intros; inversion H1.
  - econstructor.
    econstructor.
    constructor.
    constructor.
    exact H2.
  - destruct (skip_decidable c3).
    + econstructor.
      econstructor.
      constructor.
      rewrite <-H4.
      exact h1.
      rewrite H4 in h2.
      rewrite (multi_skip _ _ _ h2). exact H2.
    + assert (Hn3 : n3 < n1). {destruct n0. inversion h1. lia.}
      destruct (H0 n3 Hn3 _ _ _ _ _ _ h2 H2).
      econstructor.
      econstructor.
      apply Sseq. exact h1.
      exact H4.
      exact H9.
Qed.

Lemma imp_big_to_small `{EqDec Var} : forall c s1 s2, big_step c s1 s2 -> exists n, refl_trans n (c, s1) (skip, s2).
Proof.
  intros. induction H0.
  - exists 0. constructor.
  - exists (1 + 0). econstructor. constructor. constructor.
  - destruct IHbig_step1 as (n1 & Hn1).
    destruct IHbig_step2 as (n2 & Hn2).
    eapply seq_trans. exact Hn1. exact Hn2.
  - destruct IHbig_step as (n & Hn).
    exists (1 + n).
    econstructor.
    constructor. exact hb.
    exact Hn.
  - destruct IHbig_step as (n & Hn).
    exists (1 + n).
    econstructor.
    apply SiteF. exact hb.
    exact Hn.
  - destruct IHbig_step1 as (n1 & Hn1).
    destruct IHbig_step2 as (n2 & Hn2).
    edestruct seq_trans. exact Hn1. exact Hn2.
    econstructor.
    econstructor.
    constructor. exact hb. exact H0.
  - exists (1 + 0).
    econstructor.
    apply SwhileF. exact hb.
    constructor.
Qed.


Theorem imp_small_iff_big `{EqDec Var} : forall c s1 s2, big_step c s1 s2 <-> exists n, refl_trans n (c, s1) (skip, s2).
Proof.
  intros.
  split.
  apply imp_big_to_small.
  intros (n & Hn). eapply imp_small_to_big. exact Hn.
Qed.

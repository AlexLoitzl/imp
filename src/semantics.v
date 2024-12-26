Require Import imp.
Require Import Coq.Init.Nat.
Require Import Classes.EquivDec.
Require Import Coq.Arith.Wf_nat.

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
    small_step 2 (seq c1 c2, s1) (c2, s2)
| Sseq (s1 s2 : State) (c1 c1' c2 : Prog) (n : nat) (h : small_step n (c1, s1) (c1', s2)) (h' : c1' <> skip) :
    small_step 1 (seq c1 c2, s1) (seq c1' c2, s2)
| RiteT (s : State) (b : Bexp) (c1 c2 : Prog) (hb : eval_Bexp b s = true) :
    small_step 1 (ite b c1 c2, s) (c1, s)
| RiteF (s : State) (b : Bexp) (c1 c2 : Prog) (hb : eval_Bexp b s = false) :
    small_step 1 (ite b c1 c2, s) (c2, s)
| RwhileT (s : State) (b : Bexp) (c c : Prog) (hb : eval_Bexp b s = true) :
    small_step 1 (while b c, s) (seq c (while b c), s)
| RwhileF (s : State) (b : Bexp) (c c : Prog) (hb : eval_Bexp b s = false) :
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

(* We need to count skips otherwise we get weird programs like (skip ; skip) ; skip which need 0 steps
   Maybe just do stupid case distinctions... *)

Inductive refl_trans `{EqDec Var} : nat  -> (Prog * State) -> (Prog * State) -> Prop :=
| Refl (s : State) (c : Prog) : refl_trans 0 (c, s) (c, s)
| Trans (s1 s2 s3 : State) (c1 c2 c3 : Prog) (n1 n2 : nat) (h1 : small_step n1 (c1, s1) (c2, s2))
    (h2 : refl_trans n2 (c2, s2) (c3, s3)) : refl_trans (n1 + n2) (c1, s1) (c3, s3).

Lemma imp_small_to_big `{EqDec Var} : forall n c s1 s2, refl_trans n (c, s1) (skip, s2) -> big_step c s1 s2.
Proof.
  induction n; intros.
  - inversion H0.
    + constructor.
    + apply PeanoNat.Nat.eq_add_0 in H2 as (H2 & H2'). rewrite H2 in h1. inversion h1.
  - inversion H0. inversion h1.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.


Lemma imp_big_to_small `{EqDec Var} : forall c s1 s2, big_step c s1 s2 -> small_steps c s1 s2.
Proof. Admitted.

Theorem imp_small_iff_big `{EqDec Var} : forall c s1 s2, big_step c s1 s2 <-> small_steps c s1 s2.

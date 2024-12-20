Require Import imp.
Require Import Coq.Init.Nat.
Require Import Classes.EquivDec.

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

(* Big-step semantics *)

(* We define semantics as a relation as we cannot encode unbounded loops *)
(* Inductive big_step  *)
Inductive big_step `{EqDec Var} : Prog -> State -> State -> Prop :=
| Rskip (s : State) : big_step skip s s
| Rass (s : State) (v : Var) (a : Aexp) :
    big_step (ass v a) s (fun x => if x == v then (eval_Aexp a s) else s x)
| Rseq (s1 s2 s3 : State) (c1 c2 : Prog) (h : big_step c1 s1 s2) : big_step (seq c1 c2) s1 s3
| RiteT (s1 s2 : State) (b : Bexp) (c1 c2 : Prog) (hb : eval_Bexp b s1 = true)
    (h : big_step c1 s1 s2) : big_step (ite b c1 c2) s1 s2
| RiteF (s1 s2 : State) (b : Bexp) (c1 c2 : Prog) (hb : eval_Bexp b s1 = false)
    (h : big_step c2 s1 s2) : big_step (ite b c1 c2) s1 s2
| RwhileT (s1 s2 s3 : State) (b : Bexp) (c : Prog) (hb : eval_Bexp b s1 = true)
    (h1 : big_step c s1 s2) (h2 : big_step (while b c) s2 s3) : big_step (while b c) s1 s3
| RwhileF (s : State) (b : Bexp) (c : Prog) (hb : eval_Bexp b s = false) : big_step (while b c) s s.

Require Import imp.
Require Import Coq.Init.Nat.

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

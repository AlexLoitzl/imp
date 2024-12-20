Require Import imp.

Notation State := (Var -> nat).

Fixpoint eval_Aexp (a : Aexp) (s : State) : nat := 0.

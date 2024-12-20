Require Import String.
(* We define a deep embedding of our language as otherwise the line between operational and
 denotational semantics gets blurry *)

Parameter Var : Set.

Inductive Aexp :=
| NumE (n : nat)
| VarE (v : Var)
| Plus (a1 a2 : Aexp)
| Minus (a1 a2 : Aexp)
| Times (a1 a2 : Aexp).

Inductive Bexp :=
| TrueE
| FalseE
| LE (a1 a2 : Aexp) (* <= *)
| Neg (b : Bexp)
| And (b1 b2 : Bexp)
| Or (b1 b2 : Bexp).

Inductive Prog :=
| skip
| ass (v : Var) (a : Aexp)
| seq (c1 c2 : Prog)
| ite (b : Bexp) (c1 c2 : Prog)
| while (b : Bexp) (c : Prog).

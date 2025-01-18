
(* Types of Actions and Identifiers for (unguarded) Processes and Guarded Process, respectively *)
Parameter (Action IdP IdG: Set).

(** Mutually recursive definition of Guarded Basic Parallel Processes (gBPP) *)
(* The GuardedProcess type captures that we can combine any two guarded process without an additional
  prefix, and that a prefixed process is a guarded process *)
Inductive GuardedProcess : Set :=
| gp_zero
| gp_seq (a : Action) (p: Process)
| gp_plus (gp1 gp2 : GuardedProcess)
| gp_parall (gp1 gp2 : GuardedProcess)
| gp_id (id : IdP)

(* A process allows for unrestricted combinations and use of names. Moreover, a guarded process is a process *)
with Process : Set :=
| ebd (gp : GuardedProcess)
| p_plus (p1 p2 : Process)
| p_parall (p1 p2 : Process)
| p_id (id : IdG).

Coercion ebd : GuardedProcess >-> Process.

Notation Env := ((IdP -> Process) * (IdG -> GuardedProcess)).

(* TODO Is substitution working correctly?
  I am completely ignoring the Identity, but that seems more like operational semantics *)
Inductive ExecCtx :=
| seq_ctx (a : Action)
| plusL_ctx (gpr : GuardedProcess)
| plusR_ctx (gpl : GuardedProcess)
| parallL_ctx (gpr : GuardedProcess)
| parallR_ctx (gpl : GuardedProcess).

Definition subst (p : GuardedProcess) (ctx : ExecCtx) : GuardedProcess :=
  match ctx with
  | seq_ctx a => gp_seq a p
  | plusL_ctx gpr => gp_plus p gpr
  | plusR_ctx gpl => gp_plus gpl p
  | parallL_ctx gpr => gp_parall p gpr
  | parallR_ctx gpl => gp_parall gpl p
  end.

Inductive Tau : Set := tau.

Notation Event := (sum Action Tau).

(* TODO: I cannot seem to define this using mutual recursion because of the indices *)

Inductive stepG : GuardedProcess -> Event -> GuardedProcess -> Prop :=
| stepG_plusL (e : Event) (p1 p2 p1' : GuardedProcess) (h: stepG p1 e p1') :
    stepG (gp_plus p1 p2) e (gp_plus p1' p2)
| stepG_plusR (e : Event) (p1 p2 p2' : GuardedProcess) (h: stepG p2 e p2') :
    stepG (gp_plus p1 p2) e (gp_plus p1 p2')
| stepG_parallL (e : Event) (p1 p2 p1' : GuardedProcess) (h: stepG p1 e p1') :
    stepG (gp_parall p1 p2) e (gp_plus p1' p2)
| stepG_parallR (e : Event) (p1 p2 p2' : GuardedProcess) (h: stepG p2 e p2') :
    stepG (gp_parall p1 p2) e (gp_plus p1 p2').

Inductive step : Process -> Event -> Process -> Prop :=
| step_plusL (e : Event) (p1 p2 p1' : Process) (h: step p1 e p1') :
    step (p_plus p1 p2) e (p_plus p1' p2)
| step_plusR (e : Event) (p1 p2 p2' : Process) (h: step p2 e p2') :
    step (p_plus p1 p2) e (p_plus p1 p2')
| step_parallL (e : Event) (p1 p2 p1' : Process) (h: step p1 e p1') :
    step (p_parall p1 p2) e (p_plus p1' p2)
| step_parallR (e : Event) (p1 p2 p2' : Process) (h: step p2 e p2') :
    step (p_parall p1 p2) e (p_plus p1 p2').

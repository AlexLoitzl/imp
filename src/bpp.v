
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

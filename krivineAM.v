(*Krivine Abstract Machine - Third Part*)

(*Syntax*)

Inductive inst :=
| Access: nat -> inst
| Grab: inst
| Push: code -> inst
with code: Type :=
| cnil:   code
| cCons:  inst -> code -> code.

Inductive environment : Type := 
| nul: environment
| cons: code -> environment -> environment -> environment.


Definition state := prod (prod code environment) environment.

(*Semantics*)

Definition exec_inst (s: state): state:=
  match s with
    | (cCons (Access 0) c, cons c0 e0 e, stack) => (c0, e0, stack)
    | (cCons (Access n) c, cons c0 e0 e, stack) => (cCons (Access (n-1)) c, e, stack)
    | (cCons (Push c) c0, e, stack) => (c0, e, cons c e stack)
    | (cCons Grab c, e, cons  c0 e0 stack) => (c, cons c0 e0 e, stack)
    | s => s
  end.
(*Executing several times the code*)
Inductive mult_exec_inst : state -> state -> Prop :=
  | zero_step : forall s : state, mult_exec_inst s s
  | iPlus_step: forall s1 s2: state, mult_exec_inst (exec_inst s1) s2 -> mult_exec_inst s1 s2.

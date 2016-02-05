Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.
Require Import untypedLambda.


(*Krivine Abstract Machine*)

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
| cons: (prod code environment) -> environment -> environment.

Definition state := prod (prod code environment) environment.

Check environment_ind.

(*Semantics*)

Fixpoint exec_inst (s: state): option state:=
  match s with
    | (cCons (Access 0) c, cons (c0,e0) e, stack) => Some (c0, e0, stack)
    | (cCons (Access n) c, cons (c0,e0) e, stack) => Some (cCons (Access (n-1)) c, e, stack)
    | (cCons (Push c) c0, e, stack) => Some (c0, e, cons (c,e) stack)
    | (cCons Grab c, e, cons (c0,e0) stack) => Some (c, cons (c0,e0) e, stack)
    | _ => None
  end.

(*Compiling*)

Fixpoint compile (t: term): code :=
  match t with
      | Var n => cCons (Access n) cnil
      | Lambda t1 => cCons Grab (compile t1)
      | App t1 t2 => cCons (Push (compile t1)) (compile t2) 
  end.


Fixpoint tau_code (c: code): term :=
  match c with
    | cnil => Var 0
    | (cCons (Access n) _ ) => Var n                
    | (cCons (Push c1) c0) => App (tau_code c0) (tau_code c1)
    | (cCons Grab c0) => Lambda (tau_code c0)
  end.

Fixpoint tau_env (e: env): term :=
  match e with
    | nul
    |
  end







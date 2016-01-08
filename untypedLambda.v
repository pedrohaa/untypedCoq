Require Import ssreflect.
Require Import Arith.EqNat.

Definition var := nat.

Inductive term :=
  | Var : var -> term
  | Lambda: term -> term
  | App: term -> term -> term.

Check Lambda ( Lambda (Var 1)).

Fixpoint term_clos_aux (n : nat) (t: term): Prop :=
  match t with
    | Var v => lt v n
    | Lambda t1 => term_clos_aux (n+1) t1
    | App t1 t2 => (term_clos_aux n t1) /\ (term_clos_aux n t2)
  end.


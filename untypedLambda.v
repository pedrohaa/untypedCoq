Require Import ssreflect.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.

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

Definition term_clos (t: term): Prop := term_clos_aux 1 t.

Compute (term_clos (Lambda (Var 0))).

Fixpoint increase_k_fv (k: nat) (n:nat) (t:term): term :=
  match t with
    | Var v => if leb n v then Var (v+k) else Var v 
    | App t1 t2 => App (increase_k_fv k n t1) (increase_k_fv k n t2)
    | Lambda t1 => Lambda (increase_k_fv k (n+1) t1)
  end.

Fixpoint beta_eq_aux (k: nat) (n: nat) (t1: term) (t2: term): term :=
  match t1 with
    | Var v1 => if beq_nat v1 (n-1) then (increase_k_fv k 0 t2) else Var v1
    | App t3 t4 => App (beta_eq_aux k n t3 t2) (beta_eq_aux k n t4 t2)
    | Lambda t3 => if beq_nat 0 n then beta_eq_aux k (n+1) t3 t2 else Lambda (beta_eq_aux (k+1) (n+1) t3 (t2))
  end.

Definition beta_eq (t1: term) (t2: term): term := beta_eq_aux 0 0 t1 t2.

Compute (term_clos (App (Lambda (Lambda (Var 2))) (Lambda ( Lambda (Var 0))))).

Compute (increase_k_fv 0 0 (Lambda ( Lambda (Var 0)))).

Compute (beta_eq (Lambda (Lambda (App (Var 1) (Lambda (App (Var 0) (Var 2)))))) (Lambda (App (Var 5) (Var 0)))).
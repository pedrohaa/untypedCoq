Require Import ssreflect.
(*Require Import ssrnat.*)
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.

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

Fixpoint C_aux (k: nat) (i: nat) (t: term): Prop :=
  match t with
    | Var v => lt v i
    | App t1 t2 => (C_aux k i t1) /\ (C_aux k i t2)
    | Lambda t1 => C_aux (k+1) i t1
  end.

Definition C (i: nat) (t: term): Prop := C_aux 0 i t.

Lemma ind_Caux_pred: forall t: term, forall n k: nat,  C_aux k n t -> C_aux k (n+1) t. 
Proof.
  move => t n.
  induction t.
  move => k.
  simpl.
  move => h0.
  Search _ "trans".
  apply (Plus.lt_plus_trans v n 1).
  done.
  simpl.
  move => k h0.
  apply IHt.
  done.
  move => k.
  simpl.
  move => [h0 h1].
  split.
  apply IHt1.
  done.
  apply IHt2.
  done.
Qed.

Lemma ind_C_pred: forall t: term, forall n: nat, C n t -> C (n+1) t.
Proof.
  move => t n.
  apply (ind_Caux_pred t n 0).
Qed.

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

Fixpoint lifting (n: nat) (k: nat) (t: term): term :=
  match t with
    | Var i => if leb k i then Var (i+n) else Var i
    | App t1 t2 => App (lifting n k t1) (lifting n k t2)
    | Lambda t1 => Lambda (lifting n (k+1) t1)
  end.

Fixpoint substitution (i: nat) (t1: term) (t2: term): term :=
  match t1 with
    | Var k => if leb i k then (if beq_nat i k then lifting i 0 t2 else Var k) else Var (k-1)
    | App t3 t4 => App (substitution i t3 t2) (substitution i t4 t2)
    | Lambda t3 => Lambda (substitution (i+1) t3 t2)
  end.

(*Lemma substitution_invariance: forall t t1: term, (term_clos t) => substitution*)

Fixpoint multiple_substitution (t: term) (lt: list term) (i: nat) (length: nat): term :=
  match t with
    | Var v => if (leb i v) && (leb v (i+length-1)) then substitution v (Var v) (nth (v - i) lt (Var v))  else Var v
    | App t1 t2 => App (multiple_substitution t1 lt i length) (multiple_substitution t2 lt i length)
    | Lambda t1 => Lambda (multiple_substitution t1 lt (i+1) length)
  end.

Lemma id_substitution: forall t: term, forall i: nat, multiple_substitution t nil i 0 = t.
Proof.
  move => t.
  induction t.
  move => i.
  induction i.
  simpl.
  case v.
  simpl.
  done.
  simpl.
  done.
  simpl.
  case v.
  simpl.
  done.
  move => n.
  have:(((leb i n) && (leb (S n) (i + 0 - 0)))%bool = false).
  Search "&&".  
  apply Bool.andb_false_iff.
  admit.
  move => h0.
  rewrite h0.
  done.
  simpl.
  move => i.
  rewrite IHt.
  done.
  simpl.
  move => i.
  rewrite IHt1.
  rewrite IHt2.
  done.
Qed.

Lemma no_index_sub: forall t u: term, forall i: nat, C i t -> substitution i t u = t.
  Proof.
    move => t u.
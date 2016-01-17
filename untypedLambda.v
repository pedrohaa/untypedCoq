Require Import ssreflect.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.

Definition var := nat.

Inductive term :=
| Var : var -> term
| Lambda: term -> term
| App: term -> term -> term.

Check Lambda ( Lambda (Var 1)).

(*Is it true?*)
Lemma lambda_equivalence: forall t u: term, t = u <-> (Lambda t = Lambda u).
Proof.
  move => t u.
  split;(move => h0).
  rewrite h0.
  done.
  inversion h0.
  trivial.
Qed.

Lemma app_equivalence: forall t u v w: term, App t u = App v w <-> (t = v) /\ (u = w).
Proof.
  move => t u v w.
  split.
  move => h0.
  split.
  inversion h0.
  done.
  inversion h0.
  done.
  move => [h0 h1].
  rewrite h0.
  rewrite h1.
  done.
Qed.

Fixpoint term_clos_aux (n : nat) (t: term): Prop :=
  match t with
    | Var v => lt v n
    | Lambda t1 => term_clos_aux (n+1) t1
    | App t1 t2 => (term_clos_aux n t1) /\ (term_clos_aux n t2)
  end.

Definition term_clos (t: term): Prop := term_clos_aux 0 t.

Compute (term_clos (Lambda (Var 0))).

Fixpoint C (i: nat) (t: term): Prop :=
  match t with
    | Var v => (v < i) 
    | App t1 t2 => (C i t1) /\ (C i t2)
    | Lambda t1 => C (i+1) t1
  end.

Lemma ind_C_pred: forall t: term, forall n: nat, C n t -> C (n+1) t.
Proof.
  induction t.
  move => n.
  simpl.
  move => h0.
  Search _ (_<_).
  apply Plus.lt_plus_trans.
  done.
  move => n.
  simpl.
  move => h0.
  apply IHt.
  done.
  simpl.
  move => n.
  move => [h0 h1].
  split.
  apply IHt1.
  done.
  apply IHt2.
  done.  
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

(*
 ^ k
 |
 | n
 *)
Fixpoint lifting (n: nat) (k: nat) (t: term): term :=
  match t with
    | Var i => if leb k i then Var (i+n) else Var i
    | App t1 t2 => App (lifting n k t1) (lifting n k t2)
    | Lambda t1 => Lambda (lifting n (k+1) t1)
  end.

Fixpoint substitution_aux (k: nat) (i: nat) (t1: term) (t2: term): term :=
  match t1 with
    | Var v => if beq_nat i v then lifting k 0 t2 else Var v
    | App t3 t4 => App (substitution_aux k i t3 t2) (substitution_aux k i t4 t2)
    | Lambda t3 => Lambda (substitution_aux (k+1) (i+1) t3 t2)
  end.


Fixpoint substitution (i: nat) (t1: term) (t2: term): term :=
  match t1 with
    | Var v => if beq_nat i v then t2 else Var v
    | App t3 t4 => App (substitution i t3 t2) (substitution i t4 t2)
    | Lambda t3 => Lambda (substitution (i+1) t3 (lifting 1 0 t2))
  end.

Lemma substitution_invariance: forall (t u: term) (i: nat), (C 0 t) -> substitution i t u = t.
Proof.
  induction t.
  move => u i.
  simpl.
  move => h0.
  Search "0".
  apply Lt.lt_n_0 in h0.
  done.
  simpl.
  move => u i h0.  
  rewrite -lambda_equivalence.
  apply IHt.
  admit.
  intros.
  simpl.
  rewrite app_equivalence.
  simpl in H.
  move:H.
  move => [h0 h1].
  split.
  apply IHt1.
  done.
  apply IHt2.
  done.
Qed.
  

Fixpoint multiple_substitution (t: term) (lt: list term) (i: nat) (length: nat): term :=
  match t with
    | Var v => if (leb i v) && (leb v (i+length-1)) then substitution v (Var v) (nth (v - i) lt (Var v))  else Var v
    | App t1 t2 => App (multiple_substitution t1 lt i length) (multiple_substitution t2 lt i length)
    | Lambda t1 => Lambda (multiple_substitution t1 lt (i+1) length)
  end.

Lemma dic: forall b : bool, (b = false) \/ (b = true).
Proof.
  move => b.
  case b.
  right.
  done.
  left.
  done.
Qed.

Theorem id_substitution: forall t: term, forall i: nat, multiple_substitution t nil i 0 = t.
Proof.
  induction t.
  move => i.
  simpl.
  elim (dic (leb i v && leb v (i + 0 - 1))%bool).
  move => h0.
  rewrite h0.
  done.
  move => h0.
  rewrite h0.
  have:(beq_nat v v = true).
  Search "beq".
  apply beq_nat_true_iff.
  done.
  move => h1.
  rewrite h1.
  case (v - i).
  done.
  done.
  intro.
  simpl.
  rewrite IHt.
  done.
  intro.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  done.
Qed.

Theorem no_index_sub: forall t u: term, forall i: nat, C i t -> substitution i t u = t.
Proof.
  move => t.
  induction t.
  move => u i.
  rewrite/C.
  move => h0.
  simpl.
  have:(beq_nat i v = false).  
  Search "beq".
  apply beq_nat_false_iff.
  Search _ (_<>_).
  Search _ (_ < _).
  admit.
  move => h.
  rewrite h.
  done.
  move => u i.
  simpl.
  move => h0.  
  rewrite -lambda_equivalence.
  apply IHt.
  done.
  move => u i.
  simpl.
  move => [h0 h1].
  rewrite app_equivalence.
  split.
  apply IHt1.
  done.
  apply IHt2.
  done.  
Qed.

(*last theorem... i'll do it later*)



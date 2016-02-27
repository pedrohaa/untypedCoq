Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.

Definition var := nat.

Set Printing Universes.

(* term is of (higher) type Set since nat is of type Set*)

Inductive term :=
| Var : var -> term
| Lambda: term -> term
| App: term -> term -> term.


Check Lambda ( Lambda (Var 1)).



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

Fixpoint substitution (i: nat) (t1: term) (t2: term): term :=
  match t1 with
    | Var v => if beq_nat i v then t2 else Var v
    | App t3 t4 => App (substitution i t3 t2) (substitution i t4 t2)
    | Lambda t3 => Lambda (substitution (i+1) t3 (lifting 1 0 t2))
  end.

Lemma subs_inv: forall (t u: term) (i: nat), (C i t) -> substitution i t u = t.
Proof.
  induction t.
  simpl.
  intros.
  Search _ (_ < _).
  have:(beq_nat i v = false).
  apply beq_nat_false_iff.
  intro.
  rewrite H0 in H.
  apply Lt.lt_irrefl in H.
  done.
  move => h0.
  rewrite h0.
  done.
  simpl.
  intros.
  rewrite -lambda_equivalence.
  apply IHt.
  done.
  simpl.
  intros.
  rewrite app_equivalence.
  split.
  apply IHt1.
  apply H.
  apply IHt2.
  apply H.
Qed.

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
  apply subs_inv.
  induction i.
  simpl.
  done.
  apply ind_C_pred.
  rewrite Plus.plus_comm in IHi.
  done.
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
  
Fixpoint lift_all (n: nat) (k: nat) (l: list term): list term :=
  match l with
    | nil => nil
    | x :: xs => (lifting n k x) :: (lift_all n k xs)
  end.

Fixpoint multiple_substitution (i: nat) (t: term) (lu: list term): term :=
  match t with
    | Var v => if (leb i v) && (leb v (i+(length lu)-1)) then substitution v (Var v) (nth (v - i) lu (Var 0))  else Var v
    | App t1 t2 => App (multiple_substitution i t1 lu) (multiple_substitution i t2 lu)
    | Lambda t1 => Lambda (multiple_substitution (i+1) t1 (lift_all 1 0 lu))
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

Theorem id_substitution: forall t: term, forall i: nat, multiple_substitution i t nil = t.
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
  move: h0.
  case v.
  intro.
  Search "andb".
  apply Bool.andb_true_iff in h0.
  Search "leb_iff".
  destruct h0 as [h0 h01].
  apply leb_iff in h0.
  apply leb_iff in h01.
  simpl.
  done.
  case i.
  intros.
  apply Bool.andb_true_iff in h0.
  destruct h0 as [h0 h01].
  apply leb_iff in h0.
  apply leb_iff in h01.
  omega.
  intros.
  simpl.
  apply Bool.andb_true_iff in h0.
  destruct h0 as [h0 h01].
  apply leb_iff in h0.
  apply leb_iff in h01.
  omega.
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
  intro.
  rewrite H in h0.
  Search "lt_irrefl".
  apply Lt.lt_irrefl in h0.
  done.
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

Fixpoint all_less_i (i: nat) (lu: list term): Prop := 
  match lu with
    | nil => True
    | x :: xs => (C i x) -> (all_less_i i xs)
  end.

Check length.
Check nth.

Lemma lift_free: forall (t: term) (i k: nat), C i t -> C (i+1) (lifting 1 k t).
Proof.
  induction t.
  simpl.
  intros.
  case (leb k v).
  simpl.
  Search "plus".
  apply Plus.plus_lt_compat_r.
  done.
  simpl.
  Search "plus".
  apply Plus.lt_plus_trans.
  done.
  simpl.
  intros.
  apply IHt.
  done.
  simpl.
  intros.
  split.
  apply IHt1.
  apply H.
  apply IHt2.
  apply H.
Qed.

Lemma extract_lifting: forall (lu: list term) (j: nat) (u: term), (j < length lu) -> (nth j (lift_all 1 0 lu) u) = lifting 1 0 (nth j lu u).
Proof.
  induction lu.
  simpl.
  intros.
  Search _ (_<_).
  apply Lt.lt_n_0 in H.
  done.
  simpl.
  intros.
  induction j.
  done.
  apply IHlu.
  Search _ (_<_).
  apply (Plus.plus_lt_reg_l j (length lu) 1).
  apply H.
Qed.

Lemma lt_plus_l: forall (n m p: nat), n + p < m -> n < m.
Proof.
  induction n.
  induction m.
  simpl.
  intros.
  apply lt_n_0 in H.
  done.
  simpl.
  intros.
  Search _ (_<_).
  apply lt_0_Sn.
  intros.
  omega.
Qed.

Lemma le_plus_l: forall (n m p: nat), n + p <= m -> n <= m.
Proof.
  intros.
  omega.
Qed.

Lemma minus_dist: forall (n m p: nat), n - (m+p) = (n-m) - p.
Proof.
  intros.
  omega.
Qed.

Lemma lift_inv: forall (lu:list term), length lu = length (lift_all 1 0 lu).
Proof.
  induction lu.
  simpl.
  reflexivity.
  simpl.
  rewrite IHlu.
  reflexivity.  
Qed.

Lemma mult_sub_inv_bis: forall (t u:term) (lu:list term) (i: nat),
 (0 < length lu) -> (forall (j:nat), (j < length lu) -> C i (nth j lu (Var 0))) -> multiple_substitution i t (u :: lu) = substitution i (multiple_substitution (i+1) t lu) (u).
Proof.
  induction t.
  intros.
  simpl.
  have:(true = beq_nat v v).
  Search "beq".
  apply ( beq_nat_refl v).
  intro.
  rewrite -x.
  have:((leb (i+1) v = false) \/ (leb (i+1) v = true)).
  apply (dic (leb (i+1) v)).
  intro.
  case:x0.
  move => h0.
  rewrite h0.
  simpl.
  apply leb_iff_conv in h0.
  have:(v < i)\/(v=i).
  Search _ (_<_).
  apply le_lt_or_eq.
  rewrite ->plus_comm in h0.
  apply lt_n_Sm_le in h0.
  done.
  intro h1.
  apply or_comm in h1.
  case:h1.
  intro h1.
  rewrite h1.
  rewrite minus_diag.
  Search "leb".
  have:(leb i i = true).
  apply leb_iff.
  apply le_refl.
  intro h2.
  rewrite h2.
  simpl.
  have:(beq_nat i i = true).
  apply beq_nat_true_iff.
  reflexivity.
  intro h3.
  rewrite h3.
  have:(leb i (i + (length lu+1) -1) = true).
  apply leb_iff.
  omega.
  intro h4.
  have:i + S (length lu) - 1 = i + (length lu + 1) - 1.
  omega.
  intro.
  rewrite x0.
  rewrite h4.
  done.
  intro.
  have:leb i v = false.
  apply leb_iff_conv.
  done.
  intro.
  rewrite x0.
  simpl.
  have:beq_nat i v = false.
  rewrite beq_nat_false_iff.
  intro.
  rewrite H1 in b.
  apply lt_irrefl in b.
  done.
  intro h1.
  rewrite h1.
  done.
  intro.
  rewrite b.
  simpl.
  apply leb_iff in b.
  apply le_lt_or_eq_iff in b.
  have:i + 1 + length lu - 1 = i + (1 + length lu) - 1.
  omega.
  intro h2.
  rewrite -h2.
  have:(leb v (i + 1 + length lu - 1) = false) \/ leb v (i + 1 + length lu - 1) = true.
  apply dic.
  intro h0.
  case:h0.
  intro h1.
  rewrite h1.
  Search _ (_&&_)%bool "comm".
  rewrite Bool.andb_comm.
  simpl.
  have:(beq_nat i v = false). 
  rewrite beq_nat_false_iff.
  intro.
  rewrite H1 in b.
  case b.
  intro.
  omega.
  omega.
  intro h3.
  rewrite h3.
  done.
  intro h1.
  rewrite h1.
  rewrite Bool.andb_comm.
  simpl.
  have:leb i v = true.
  have:(i+1) <= v.
  Search _ (_<=_) "or".
  apply le_lt_or_eq_iff.
  done.
  intro h3.
  apply leb_iff.
  apply (le_plus_l i v 1).
  done.
  intro h3.
  rewrite h3.
  rewrite NPeano.Nat.sub_add_distr.
  destruct (v - i) eqn:h4.
  apply NPeano.Nat.sub_0_le in h4.
  omega.
  simpl.
  rewrite -minus_n_O.
  symmetry.
  apply no_index_sub.
  apply H0.
  apply leb_iff in h1.
  apply leb_iff in h3.
  omega.
  intros.
  simpl.
  rewrite -lambda_equivalence.
  (*Find a way to deal with the lifting operation*)
  apply (IHt (lifting 1 0 u) (lift_all 1 0 lu) (i+1)).
  rewrite -lift_inv.
  done.
  intros.
  rewrite -lift_inv in H1.
  rewrite (extract_lifting).
  apply lift_free.
  apply H0.
  done.
  done.
  intros.
  simpl.
  rewrite app_equivalence.
  split.
  apply (IHt1 u lu i).
  done.
  done.
  apply (IHt2 u lu i).
  done.
  done.
Qed.
  
Lemma mult_sub_inv: forall (t u:term) (lu:list term) (i: nat),
 (forall (j:nat), (j < length lu) -> C i (nth j lu (Var 0))) -> multiple_substitution i t (u :: lu) = substitution i (multiple_substitution (i+1) t (lu)) (u).
Proof.
  induction lu.
  move:u.
  induction t.
  intros.
  rewrite id_substitution.
  unfold multiple_substitution.
  have:i + 1 - 1 = i.
  omega.
  intro h0.
  rewrite h0.
  have: ((leb i v && leb v i)%bool = false) \/ (leb i v && leb v i)%bool = true. 
  apply dic.
  intro h1.
  case:h1.
  intro h1.
  rewrite h1.
  simpl.
  apply Bool.andb_false_iff in h1.
  case:h1.
  intro h1.
  apply leb_iff_conv in h1.
  have: beq_nat i v = false.
  apply beq_nat_false_iff.
  omega.
  intro h2.
  rewrite h2.
  trivial.
  intro h1.
  apply leb_iff_conv in h1.
  have: beq_nat v i = false.
  apply beq_nat_false_iff.
  omega.
  intro h2.
  apply beq_nat_false_iff in h2.
  apply not_eq_sym in h2.
  apply beq_nat_false_iff in h2.
  rewrite h2.
  trivial.
  intro h1.
  rewrite h1.
  apply Bool.andb_true_iff in h1.
  have: i = v.
  destruct h1 as [h1 h2].
  apply leb_iff in h1.
  apply leb_iff in h2.
  omega.
  intro h2.
  have : v - i = 0.
  omega.
  intro h3.
  rewrite h3.
  simpl.
  rewrite h2.
  trivial.
  intros.
  simpl.
  rewrite -lambda_equivalence.
  apply IHt.
  intros.
  apply ind_C_pred.
  apply H.
  trivial.
  intros.
  simpl.
  rewrite app_equivalence.
  split.
  apply IHt1.
  done.
  apply IHt2.
  done.
  intros.
  apply (mult_sub_inv_bis t u (a::lu) i).
  simpl.
  omega.
  intros.
  apply H.
  done.
Qed.

(*new part*)

Inductive reducesInOneTo: term -> term -> Prop :=
  | appLeft: forall (t u v: term), reducesInOneTo t u -> reducesInOneTo (App t v) (App u v)  
  | appRight: forall (t u v: term), reducesInOneTo t u -> reducesInOneTo (App v t) (App v u)  
  | addLamb: forall (t u:term), reducesInOneTo t u -> reducesInOneTo (Lambda t) (Lambda u)
  | removeLamb: forall (t u: term), reducesInOneTo (App (Lambda t) u) (substitution 0 t u).

Inductive reduces: term -> term -> Prop :=
  | sym: forall (t: term), reduces t t
  | ind: forall (t u v: term), reducesInOneTo t u -> reduces u v -> reduces t v.


Inductive reducesN: nat -> term -> term -> Prop :=
  | symN: forall (t: term), reducesN 0 t t
  | indN: forall n: nat, forall (t u v: term), reducesInOneTo t u -> reducesN n u v -> reducesN (S n) t v.

Fixpoint reducesInN (t: term) (u: term) (n: nat): Prop :=
  match n with
    | 0 => t = u
    (*| 1 => reducesInOneTo t u*)
    | S m => exists v: term, (reducesInOneTo t v /\ reducesInN v u m)
  end.


Lemma r_equivalence: forall (t u: term), reduces t u -> (exists (n: nat), reducesInN t u n).
  Check (reduces_ind).
  apply (reduces_ind (fun u v: term => exists n: nat, reducesInN u v n)); intros.
  exists 0.
  simpl. trivial.
  elim H1.
  intros.
  exists (S x).
  unfold reducesInN. exists u. split. trivial. trivial.
Save.  

(*Context closure*)

Lemma app_left: forall (t u v: term) (n: nat), (reducesInN t u n) -> reducesInN (App t v) (App u v) n.
Proof.
  move => t u v n.
  move: t u v.
  induction n.
  simpl.
  move => t u v h0.
  rewrite h0.
  done.
  move => t u v.
  move:IHn.
  simpl.
  move => IHn.
  move => h0.
  case h0.
  move => v0 [h1 h2].  
  apply (appLeft t v0 v) in h1.
  exists (App v0 v).
  split.
  done.
  apply IHn.
  done.
Qed.

Lemma app_right: forall (t u v: term) (n: nat), (reducesInN t u n) -> reducesInN (App v t) (App v u) n.
Proof.
  move => t u v n.
  move: t u v.
  induction n.
  simpl.
  move => t u v h0.
  rewrite h0.
  done.
  move => t u v.
  move:IHn.
  simpl.
  move => IHn.
  move => h0.
  case h0.
  move => v0 [h1 h2].  
  apply (appRight t v0 v) in h1.
  exists (App v v0).
  split.
  done.
  apply IHn.
  done.
Qed.

Lemma add_Lamb: forall (t u:term) (n: nat), reducesInN t u n -> reducesInN (Lambda t) (Lambda u) n.
Proof.
  move => t u n.
  move: t u.
  induction n.
  simpl.
  move => t u h0.
  rewrite h0.
  done.
  move => t u.
  move:IHn.
  simpl.
  move => IHn.
  move => h0.
  case h0.
  move => v0 [h1 h2].  
  apply (addLamb t v0) in h1.
  exists (Lambda v0).
  split.
  done.
  apply IHn.
  done.
Qed.

Lemma test: forall t: term, reduces t t /\ exists n : nat, reducesInN t t n.
Proof.
  intros.
  split.
  apply sym.
  exists 0.
  done.
Qed.
  
Lemma red_equivalence: forall (t u: term), reduces t u <-> (exists (n: nat), reducesInN t u n).
Proof.
  intros.
  split.
  Check (reduces_ind).
  move => h0.
  
  apply (reduces_ind ( fun t u => exists n : nat, reducesInN t u n)).
  intros.
  exists 0.
  simpl.
  done.
  intros.
  case H1. intros.
  exists (S x).
  simpl.
  exists u0.
  split. trivial. trivial.
  done.
  move => h0.
  case:h0.  
  move => n.
  move: t u.
  induction n.
  simpl.
  move => t u h1.
  rewrite h1.
  apply sym.
  move => t u.
  induction n.
  simpl.
  move => h0.
  apply (ind t u).
  case h0.
  move => x [h1 h2].
  rewrite -h2.
  done.
  apply sym.
  move => h0.
  case h0.
  move => w [h1 h2].
  apply (ind t w).
  done.
  apply (IHn w u).
  done.
Qed.


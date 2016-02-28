Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.
Require Import untypedLambda.

(*Question 1.4.2*)
Theorem no_index_sub: forall (t u: term) (i: nat), (C i t) -> substitution i t u = t.
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
  apply no_index_sub.
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

(*Used for case analysis in if's*)
Lemma dic: forall b : bool, (b = false) \/ (b = true).
Proof.
  move => b.
  case b.
  right.
  done.
  left.
  done.
Qed.

(*Question 1.4.1*)
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

(*Lifting and arithmetic resuts*)
(*-----------------------------*)

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

(*-----------------------------*)

(*Question 1.4.3*)
(*Case when lu is non empty*)
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

(*General case*)
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


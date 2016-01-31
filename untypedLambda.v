Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.

Definition var := nat.

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
  



(*Deprecated*)
Fixpoint increase_k_fv (k: nat) (n:nat) (t:term): term :=
  match t with
    | Var v => if leb n v then Var (v+k) else Var v 
    | App t1 t2 => App (increase_k_fv k n t1) (increase_k_fv k n t2)
    | Lambda t1 => Lambda (increase_k_fv k (n+1) t1)
  end.




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



(*Deprecated*)
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

Fixpoint multiple_substitution (t: term) (lu: list term) (i: nat) (length: nat): term :=
  match t with
    | Var v => if (leb i v) && (leb v (i+length-1)) then substitution v (Var v) (nth (v - i) lu (Var v))  else Var v
    | App t1 t2 => App (multiple_substitution t1 lu i length) (multiple_substitution t2 lu i length)
    | Lambda t1 => Lambda (multiple_substitution t1 (lift_all 1 0 lu) (i+1) length)
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

(*last theorem... i'll do it later*)

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

Check nth.
Check hd.
Lemma mult_sub_inv_bisbis: forall (t:term) (lu:list term) (i k:nat),
  (1 <= k) -> (k < length lu) -> C i (nth k lu (Var 0)) -> 
  multiple_substitution t lu i (length lu) = substitution i (multiple_substitution t (tl lu) (i+1) (length lu - 1)) (hd (Var 0) lu).

Proof.
  induction t.
  intros.
  simpl.
  have: beq_nat v v = true.
  Search "beq".
  rewrite (beq_nat_refl v).
  done.
  intro h.
  rewrite h.
  destruct h.
  case (dic (leb i v)).

  intro h1.
  rewrite h1.
  simpl.
  have: leb (i+1) v = false.
  move:h1.
  rewrite ?leb_iff_conv.
  Search "plus_comm".
  rewrite plus_comm.
  simpl.
  Search _(?x < ?y -> ?x < S ?y).
  apply lt_S.
  intro h2.
  rewrite h2.
  simpl.
  apply leb_iff_conv in h1.
  Search "beq".
  Search _(?x<?y -> ?x<>?y).
  Search "lt_neq".
  apply NPeano.Nat.lt_neq in h1.
  Search _(?x<>?y -> ?y<>?x).
  apply not_eq_sym in h1.
  apply beq_nat_false_iff in h1.
  rewrite h1.
  done.
  intro.
  rewrite H2.
  simpl.
  case (dic (leb v (i+length lu - 1))).
  intro h.
  rewrite h.
  rewrite <-plus_comm.
  Search "plus".
  simpl.
  Search "minus".
  rewrite -minus_n_O.
  Search "assoc".
  rewrite -NPeano.Nat.add_sub_assoc in h.
  rewrite h.
  Search "false".
  rewrite Bool.andb_false_r.
  simpl.
  induction lu.
  simpl in H0.
  Search "n_0".
  apply lt_n_0 in H0.
  done.
  simpl in h.
  rewrite -minus_n_O in h.
  Search "leb_iff".
  apply leb_iff_conv in h.
  have: beq_nat i v = false.
  rewrite beq_nat_false_iff.
  apply leb_iff in H2.
  Search "le_lt_add_l".
  Search _(_<>_).
  apply NPeano.Nat.lt_neq.
  Check length lu.
  apply (NPeano.Nat.le_lt_add_lt 0 (length lu)).
  Search _(0<=_).
  apply le_0_n.

  rewrite (plus_comm v 0).
  simpl.
  done.
  intro h1.
  rewrite h1.
  done.
  Search _(?x<_->S ?x<=_).
  apply le_lt_n_Sm in H.
  apply lt_le_S in H0.
  Search "le_trans".
  apply (lt_le_trans 1 (S k) (length lu)) in H0.
  Search "lt_le".
  apply lt_le_weak.
  done.
  done.
  intros.
  rewrite H3.
  simpl.
  
  
Abort.

Lemma mult_sub_inv_bis: forall (t u:term) (lu:list term) (i: nat),
 (forall (j:nat) (u:term), (j < length lu) -> C i (nth j lu u)) -> multiple_substitution t (u :: lu) i (length lu) = substitution i (multiple_substitution t (lu) (i+1) (length lu - 1)) (u).
Proof.
  induction t.
  intros.
  simpl.
  have:(true = beq_nat v v).
  Search "beq".
  apply ( beq_nat_refl v).
  intro.
  rewrite -x.
  have:((leb i v = false) \/ (leb i v = true)).
  apply (dic (leb i v)).
  intro.
  case:x0.
  move => h0.
  rewrite h0.
  simpl.
  have:(leb (i + 1) v = false).
  Search "ltb".
  apply leb_correct_conv.
  apply (leb_iff_conv v i) in h0.
  Search _ (_<_).
  apply (Plus.lt_plus_trans).
  done.
  move => h1.
  rewrite h1.  
  simpl.
  Search "beq".
  have:(beq_nat i v = false).
  apply beq_nat_false_iff.
  intro.
  rewrite H0 in h0.
  apply leb_iff_conv in h0.
  apply Lt.lt_irrefl in h0.
  done.
  intro.
  rewrite x0.
  done.
  move => h0.
  rewrite h0.
  simpl.
  have:(leb v (i + length lu - 1) = false \/ leb v (i + length lu - 1) = true).
  apply dic.
  intros.
  case:x0.
  intro.
  rewrite a.
  have:(leb (i+1) v && leb v (i + 1 + (length lu - 1) - 1))%bool = false.
  
  (*I have to simplify the expression*)
  induction lu.
  simpl.
  rewrite -plus_n_O.
  case (dic (leb (i+1) v)).
  intro.
  rewrite H0.
  done.
  intro.
  have: leb v (i+1-1) = false.
  rewrite -NPeano.Nat.add_sub_assoc.
  simpl.
  rewrite -plus_n_O.
  rewrite leb_iff_conv.
  apply leb_iff in H0.
  rewrite plus_comm in H0.
  Search "lt" "S".
  apply le_lt_n_Sm in H0.
  apply lt_S_n in H0.
  done.
  done.
  intro.
  rewrite x0.
  rewrite Bool.andb_false_r.
  done.
  simpl.
  rewrite -minus_n_O.
  simpl in a.
  rewrite -NPeano.Nat.add_sub_assoc in a.
  Search _(S _ - S _).
  rewrite (NPeano.Nat.sub_succ (length lu) 0) in a.
  rewrite -minus_n_O in a.
  rewrite -plus_assoc.
  rewrite -NPeano.Nat.add_sub_assoc.
  rewrite (plus_comm 1 (length lu)).
  rewrite -NPeano.Nat.add_sub_assoc.
  rewrite minus_diag.
  rewrite -plus_n_O.
  rewrite a.
  rewrite Bool.andb_false_r.
  done.  
  done.
  Search _(?x<=?x +_).
  apply le_plus_l.
  Search "le" "S".
  apply le_n_S.
  Search "le".
  apply le_0_n.

(*Done. -- Chet*)  

  intro.
  rewrite x0.
  simpl.
  (*We have i < i + length lu - 1 < v => i < v => beq_nat i v = false*)
  have:(beq_nat i v = false).
  admit.
  intro x2.
  rewrite x2.
  done.
  intro.
  have:(i <= v).
  Search "leb".
  apply leb_iff.
  done.
  move => h1.
  apply Lt.le_lt_or_eq_iff in h1.
  apply or_comm in h1.
  case h1.
  intro.
  have:(i - i = 0).
  Search _ (_-_).
  apply Minus.minus_diag.
  intro.
  rewrite -H0.
  rewrite x0.
  have:(leb (i+1) i = false).
  Search "leb".
  apply leb_iff_conv.
  Search _ (_<_).
  rewrite Plus.plus_comm.
  apply Lt.lt_n_Sn.
  intro.
  rewrite x1.
  simpl.
  rewrite -beq_nat_refl.
  have:(leb i (i + length lu - 1) = true).
  apply leb_iff.
  (*Since length lu - 1 > 0, we have the inequality*)
  admit.
  intro.
  rewrite x2.
  done.
  intros.
  (*since m >= i, S m - i will be a natural number*)
  have:(v - i > 0).
  Search _ (_>_).
  admit.
  intro.
  rewrite b.
  have:(exists m, v - i = 1+m).
  admit.
  intro.
  case x1.
  intros.
  rewrite H1.
  simpl.
  have:((leb (i + 1) v && leb v (i + 1 + (length lu - 1) - 1))%bool = true).
  admit.
  intro.
  rewrite x3.
  have:(substitution i (nth (v - (i + 1)) lu (Var v)) u = (nth (v - (i + 1)) lu (Var v))).
  apply no_index_sub.
  apply H.
  rewrite plus_comm.
  rewrite plus_comm in b.
  apply leb_iff in b.
  Search "minus".
  (*trivial*)
  admit.
  intros.
  rewrite x4.
  have:(v - (i + 1) = x2).
  admit.
  intro.
  rewrite x5.
  done.
  intros.
  simpl.
  rewrite -lambda_equivalence.
  (*Find a way to deal with the lifting operation*)
  have:(length lu = length (lift_all 1 0 lu)).
  admit.
  move => h0.
  rewrite h0.
  apply (IHt (lifting 1 0 u) (lift_all 1 0 lu) (i+1)).
  rewrite -h0.
  intros.
  rewrite (extract_lifting).
  apply lift_free.
  apply H.
  done.
  done.
  intros.
  simpl.
  rewrite app_equivalence.
  split.
  apply (IHt1 u lu i).
  done.
  apply (IHt2 u lu i).
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

(*Krivine Abstract Machine*)

(*Syntax*)

(*Inductive inst :=
| Access: nat -> inst
| Grab: inst
| Push: list inst -> inst.

Definition code := list inst.*)


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

Fixpoint tau_env (e: env): 







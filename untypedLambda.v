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
  
Check nth.
Check lt.

Fixpoint lifting_list (n:nat) (k:nat) (lst:list term) : list term :=
  match lst with
    |nil => nil
    |h::t => (lifting n k h) :: (lifting_list n k t)
end.

Fixpoint multiple_substitution (t: term) (lst: list term) (i: nat) (length: nat): term :=
  match t with
    | Var v => if (leb i v) && (leb v (i+length-1)) then substitution v (Var v) (nth (v - i) lst (Var v)) else Var v
    | App t1 t2 => App (multiple_substitution t1 lst i length) (multiple_substitution t2 lst i length)
    | Lambda t1 => Lambda (multiple_substitution t1 (lifting_list 1 0 lst) (i+1) length)
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
Lemma mult_sub_inv_bis: forall (t:term) (lu:list term) (i k:nat),
  (k >= 1) -> C i (nth k lu (Var 0)) -> multiple_substitution t lu i (length lu) = substitution i (multiple_substitution t (tl lu) (i+1) (length lu - 1)) (hd (Var 0) lu). 
Proof.
  

Lemma mult_sub_inv: forall (t: term) (k i: nat) (lu: list term), k >= 1 -> (k < length lu) -> all_less_i i lu -> multiple_substitution t lu i (length lu) = substitution i (multiple_substitution t (tl lu) (i-1) (length lu - 1)) (hd (Var 0) lu) .
Proof.

Qed.


Fixpoint multiple_substitution (t: term) (lt: list term) (i: nat) (length: nat): term :=
                                                                                                        
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
| Push: code -> inst.
with code: Type :=
| cnil:   code
| cCons:  instruction -> code -> code.

Inductive environment : Type := 
| nul: environment
| cons: (prod code environment) -> environment -> environment.

Definition state := prod (prod code environment) environment.

Check environment_ind.

(*Semantics*)

Fixpoint exec_inst (s: state): option state:=
  match s with
    | ((Access 0)::c, cons (c0,e0) e, stack) => Some (c0, e0, stack)
    | ((Access n)::c, cons (c0,e0) e, stack) => Some ((Access (n-1)) :: c, e, stack)
    | ((Push c)::c0, e, stack) => Some (c0, e, cons (c,e) stack)
    | (Grab::c, e, cons (c0,e0) stack) => Some (c, cons (c0,e0) e, stack)
    | _ => None
  end.

(*Compiling*)

Fixpoint compile (t: term): code :=
  match t with
      | Var n => (Access n) :: nil
      | Lambda t1 => Grab :: (compile t1)
      | App t1 t2 => (Push (compile t1)) :: (compile t2) 
  end.


Fixpoint tau (c: code) {struct c}: term :=
  match c with
    | nil => Var 0
    | ((Push c1) :: c0) => App (tau c0) (tau c1)
    | _ => Var 0
(*    | (Grab :: c0) => Lambda (tau c0)
    | (Access n :: _) => Var n*)
  end.
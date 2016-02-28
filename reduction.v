Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.
Require Import untypedLambda.
Require Import substitution.

(*Beta reduction definition - Second Part*)
Inductive reducesInOneTo: term -> term -> Prop :=
  | appLeft: forall (t u v: term), reducesInOneTo t u -> reducesInOneTo (App t v) (App u v)  
  | appRight: forall (t u v: term), reducesInOneTo t u -> reducesInOneTo (App v t) (App v u)  
  | addLamb: forall (t u:term), reducesInOneTo t u -> reducesInOneTo (Lambda t) (Lambda u)
  | removeLamb: forall (t u: term), reducesInOneTo (App (Lambda t) u) (substitution 0 t u).

(*Transitive closure relation*)
Inductive reduces: term -> term -> Prop :=
  | sym: forall (t: term), reduces t t
  | ind: forall (t u v: term), reducesInOneTo t u -> reduces u v -> reduces t v.

(*Another definition which we'll show that they're equivalent*)
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
  
Lemma red_equivalence: forall (t u: term), reduces t u <-> (exists (n: nat), reducesInN t u n).
Proof.
  intros.
  split.
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


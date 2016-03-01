Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.

Inductive typ :=
  | Tnat : typ
  | Tarrow : typ -> typ -> typ.

Inductive term :=
  | Var : nat -> term
  | ConstNat : nat -> term
  | App : term -> term -> term
  | Lambda : typ -> term -> term.

Check nth.
Check (list).
Definition context (t: Set) := list (option t).


Lemma lambda_equivalence: forall (t u: term) (ty: typ), t = u <-> (Lambda ty t = Lambda ty u).
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


Fixpoint omap (oty: option typ)  (ty: typ) : option typ:=
  match oty with
    | None => None
    | Some t => Some (Tarrow (ty) (t)) 
  end.

Fixpoint type (ctx: list typ) (t: term) : option typ :=
  match t with
    | Var n => nth_error ctx n
    | ConstNat _ => Some Tnat 
    | App t1 t2 => if type ctx t1 is Some (Tarrow t1l t1r) then
                     if type ctx t2 is Some t1l then Some t1r
                     else None
                   else None
    | Lambda ty t => omap (type (ty :: ctx) t) ty
  end.


Fixpoint C (i: nat) (t: term): Prop :=
  match t with
    | Var v => (v < i)
    | ConstNat v => True
    | App t1 t2 => (C i t1) /\ (C i t2)
    | Lambda ty t1 => C (i+1) t1
  end.

(*Question 1.2*)
Lemma ind_C_pred: forall t: term, forall n: nat, C n t -> C (n+1) t.
Proof.
  induction t; simpl; intros.
  omega; trivial.
  trivial.
  split.
  apply IHt1.
  by destruct H.
  apply IHt2. by destruct H.
  by apply IHt.
Qed.


Fixpoint lifting (n: nat) (k: nat) (t: term): term :=
  match t with
    | Var i => if leb k i then Var (i+n) else Var i
    | ConstNat i => ConstNat i
    | App t1 t2 => App (lifting n k t1) (lifting n k t2)
    | Lambda ty t1 => Lambda ty (lifting n (k+1) t1)
  end.

Fixpoint substitution (i: nat) (t1: term) (t2: term): term :=
  match t1 with
    | Var v => if beq_nat i v then t2 else Var v
    | ConstNat i => ConstNat i
    | App t3 t4 => App (substitution i t3 t2) (substitution i t4 t2)
    | Lambda ty t3 => Lambda ty (substitution (i+1) t3 (lifting 1 0 t2))
  end.


(*Question 1.4.2*)
Theorem no_index_sub: forall (t u: term) (i: nat), (C i t) -> substitution i t u = t.
Proof.
  induction t; simpl; intros.
  have:(beq_nat i n = false).
  apply beq_nat_false_iff.
  omega.
  move => h0.
  by rewrite h0.
  trivial.
  rewrite app_equivalence; split.
  apply IHt1.
  apply H.
  apply IHt2.
  apply H.
  apply lambda_equivalence.
  by apply IHt.
Qed.

Definition has_type (ctx: list typ) (t: term) := exists ty: typ, type ctx t = Some ty.

Lemma nth_of_list: forall (A: Type) (l: list A) (n: nat), n < length l <-> exists a: A, nth_error l n = Some a. 
Proof.
  intros A l.
  split.
  move: n.
  induction l; simpl.
  intros; omega.
  intro; case n; simpl.
  intros.
  exists a.
  done.
  intros.
  apply IHl.
  omega.
  intro h0.
  case:h0.
  move: n.
  induction l; simpl.
  intros.
  have:nth_error nil n = None.
  intros.
  induction n.
  by simpl.
  by simpl.
  intro.
  by rewrite x0 in p.
  intro.
  case:n; simpl.
  intros.
  omega.
  intros.
  have: n < (length l) -> S n < S (length l).
  omega.
  intro h0; apply h0.
  by apply (IHl _ x).
Qed.

Lemma app_is_typed: forall (t1 t2: term) (ctx: list typ), has_type ctx (App t1 t2) -> has_type ctx t1 /\ has_type ctx t2.
Proof.
  unfold has_type.
  intros.
  split.
  case H.
  intro.
  simpl.
  case (type ctx t1).
  intros.  
    by exists t.
  intros.            
  by exists x.
  case H.
  simpl.
  case (type ctx t2).
  case (type ctx t1).
  intro.
  case t.
  intros.
  done.
  intros.
  by exists t4.
  intros.
  done.
  case (type ctx t1).
  intro.
  case t.
  done.
  done.
  done.
Qed.  

Lemma omap_eq: forall (oty: option typ) (ty: typ), (exists t0:typ, omap oty ty = Some t0) -> (exists t1:typ, oty = Some t1).
Proof.
  intros.
  case:H.
  intro.
  unfold omap.
  case oty.
  intros.
  by exists t.
  done.
Qed.


(*The converse is not true*)
Lemma typable_implies_closed: forall (t: term) (ctx: list typ), has_type ctx t -> C (length ctx) t.
Proof.
  induction t; simpl.
  unfold has_type.
  simpl.
  intros.
  case H.
  intros.
  induction ctx; simpl.
  have:nth_error nil n = None.
  intros.
  induction n.
  by simpl.  simpl.
  by simpl.
  intro h0.
  by rewrite h0 in H0.  
  apply nth_of_list in H.
  done.
  intro.
  done.
  unfold has_type.
  intros.
  case H.
  intros.
  split.
  apply IHt1.
  apply (app_is_typed t1 t2 ctx).
  done.
  apply IHt2.
  by apply (app_is_typed t1 t2 ctx).
  intro.
  unfold has_type.
  simpl.
  intros.
  case:H.
  intros x H0.
  rewrite plus_comm.
  apply (IHt (t::ctx)).
  unfold has_type.
  apply (omap_eq _ t).
  by exists x.
Qed.

Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.
Require Import untypedLambda.

(*Krivine Abstract Machine*)

(*Syntax*)

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

Check cons (cnil,nul) nul.

(*Semantics*)

Fixpoint exec_inst (s: state): state:=
  match s with
    | (cCons (Access 0) c, cons (c0,e0) e, stack) => (c0, e0, stack)
    | (cCons (Access n) c, cons (c0,e0) e, stack) => (cCons (Access (n-1)) c, e, stack)
    | (cCons (Push c) c0, e, stack) => (c0, e, cons (c,e) stack)
    | (cCons Grab c, e, cons (c0,e0) stack) => (c, cons (c0,e0) e, stack)
    | s => s
  end.

(*Compiling*)

Fixpoint compile (t: term): code :=
  match t with
      | Var n => cCons (Access n) cnil
      | Lambda t1 => cCons Grab (compile t1)
      | App t1 t2 => cCons (Push (compile t2)) (compile t1) 
  end.


Fixpoint tau_code (c: code): term :=
  match c with
    | cnil => Var 0
    | (cCons (Access n) _ ) => Var n                
    | (cCons (Push c1) c0) => App (tau_code c0) (tau_code c1)
    | (cCons Grab c0) => Lambda (tau_code c0)
  end.

Check multiple_substitution.

Fixpoint tau_env (e: environment): list term :=
  match e with
    | nul => nil
    | cons (c0, e0) e1 =>
      (multiple_substitution (tau_code c0) (tau_env e0) 0 (length (tau_env e0))) :: tau_env e1
  end.

Check state.

Fixpoint transform_stk (stk: environment): list term :=
  match stk with
      | cons (c0, e0) nul => multiple_substitution (tau_code c0) (tau_env e0) 0 (length (tau_env e0)) :: nil
      | cons (c0, e0) e1 => (multiple_substitution (tau_code c0) (tau_env e0) 0 (length (tau_env e0))) :: (transform_stk e1)
      | nul => nil
  end.

Check fold_left.

Fixpoint fold_left_bis (f: term -> term -> term) (l:list term): term :=
  fold_left f (removelast l) (last l (Var 0)).

Fixpoint tau (s: state): term :=
  match s with
    | (c, e, stk) =>
      match stk with
        | nul => multiple_substitution (tau_code c) (tau_env e) 0 (length (tau_env e))
        | stk => fold_left_bis (fun t1 t2 => App t1 t2) (multiple_substitution (tau_code c) (tau_env e) 0 (length (tau_env e)) :: (transform_stk stk))
      end
  end.

(*Compiling results*)


Lemma tau_nil_env: forall t: term, tau (compile t, nul, nul) = tau_code (compile t).
Proof.
  induction t.
  simpl.
  have: beq_nat v v = true.
  apply beq_nat_true_iff.
  reflexivity.
  intro h0.
  rewrite h0.
  rewrite -minus_n_O.
  have: leb v 0 = false \/ leb v 0 = true.
  apply dic.
  intro h1.
  case:h1.
  intro h1.
  rewrite h1.
  trivial.
  intro h1.
  rewrite h1.
  case v.
  done.
  done.
  simpl.
  rewrite -lambda_equivalence.
  apply id_substitution.
  simpl.
  rewrite app_equivalence.
  split.
  apply id_substitution.
  apply id_substitution.
Qed.
  
Theorem invert_comp: forall (t: term), tau (compile t, nul, nul) = t.
Proof.
  induction t.
  simpl.
  have: beq_nat v v = true.
  apply beq_nat_true_iff.
  reflexivity.
  intro h0.
  rewrite h0.
  rewrite -minus_n_O.
  have: leb v 0 = false \/ leb v 0 = true.
  apply dic.
  intro h1.
  case:h1.
  intro h1.
  rewrite h1.
  trivial.
  intro h1.
  rewrite h1.
  case v.
  done.
  done.
  simpl.
  rewrite -lambda_equivalence.
  rewrite tau_nil_env in IHt.
  rewrite IHt.
  apply id_substitution.
  simpl.
  rewrite app_equivalence.
  rewrite tau_nil_env in IHt1.
  rewrite tau_nil_env in IHt2.
  split.
  rewrite IHt1.
  apply id_substitution.
  rewrite IHt2.
  apply id_substitution.
Qed.

(*Correct state*)

Fixpoint length (e: environment): nat :=
  match e with
    | nul => 0
    | cons (c0, e0) e1 => 1 + (length e1)
  end.

Fixpoint correct_stk (stk: environment): Prop:=
  match stk with
    | nul => True
    | cons (c0, e0) e => (correct_stk e0) /\ (correct_stk e) /\ (C (length e0) (tau_code c0)) 
  end.

Fixpoint correct_state (s: state): Prop:=
  match s with
   | (c, e, stk) => (correct_stk e) /\ (correct_stk stk) /\ (C (length e) (tau_code c))
  end.

Theorem transition_inv_1: forall (c c0: code) (e e0 stack: environment), correct_state ((cCons (Access 0) c, cons (c0,e0) e, stack)) -> correct_state  (c0, e0, stack).
Proof.
  simpl.
  intros.
  split.
  apply H.
  split.
  apply H.
  apply H.
Qed.

Theorem transition_inv_2: forall (c c0: code) (e e0 stack: environment) (n: nat), (n > 0) -> correct_state (cCons (Access n) c, cons (c0,e0) e, stack) -> correct_state (cCons (Access (n-1)) c, e, stack).
Proof.
  simpl.
  intros.
  split.  
  apply H0.
  split.
  apply H0.
  destruct H0.
  destruct H1.
  omega.
Qed.

Theorem transition_inv_3: forall (c c0: code) (e stack: environment), correct_state (cCons (Push c) c0, e, stack) -> correct_state (c0, e, cons (c,e) stack).
Proof.
  simpl.  
  intros.
  split.
  apply H.
  split.
  split.
  apply H.
  split.
  apply H.
  apply H.
  apply H.  
Qed.

Theorem transition_inv_4: forall (c c0: code) (e e0 stack: environment), correct_state (cCons Grab c, e, cons (c0,e0) stack) -> correct_state (c, cons (c0,e0) e, stack).
Proof.
  simpl.
  intros.
  split.
  split.
  apply H.
  split.
  apply H.
  apply H.
  split.
  apply H.
  rewrite plus_comm in H.
  apply H.
Qed.

Theorem correct_invariance: forall s: state, correct_state s -> correct_state (exec_inst s).
Proof.
  intro.
  destruct s.
  destruct p.
  move: e e0.
  induction c.
  move => e e0.
  case e0.
  case e.
  simpl.
  done.
  simpl.
  done.
  simpl.
  done.
  case i.
  intros n e e0.
  case e0.
  case n.
  simpl.
  done.
  simpl.
  done.
  intros p e1.
  destruct p.
  unfold exec_inst.
  case n.
  apply transition_inv_1.
  intro.
  apply transition_inv_2.
  omega.
  unfold exec_inst.
  intros e e0.
  case e.
  done.
  intros p e1.
  destruct p.
  apply transition_inv_4.
  intros c0 e e0.
  apply transition_inv_3.
Qed.

Lemma toy_lemma: forall (c c0: code) (e s: environment), correct_state (cCons (Push c0) c,e,s) -> reduces (tau (cCons (Push c0) c,e,s)) (tau (c, e, cons (c0, e) s)).
Proof.
  intros.
  simpl.
  case s.
  apply sym.
  intros.
  destruct p.
  simpl in H.
  destruct H as [h0 [h1 [h2 h3]]].
  apply red_equivalence.
  exists 0.
  simpl.
  done.
Qed.

Theorem correct_confluence: forall s: state, correct_state s -> reduces (tau s) (tau (exec_inst s)).
Proof.
  induction s.
  destruct a.
  simpl.



  (*Unify every transition*)










  
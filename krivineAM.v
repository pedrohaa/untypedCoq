Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.
Require Import untypedLambda.

Set Printing Universes.

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


Check inst->code.
Check Set.
Check code.
Check Set -> Type.
Check environment.
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

Fixpoint tau (s: state): term :=
  match s with
    | (c, e, stk) =>
      match stk with
        | nul => multiple_substitution (tau_code c) (tau_env e) 0 (length (tau_env e))
        | stk => fold_left (fun t1 t2 => App t1 t2) (transform_stk stk) (multiple_substitution (tau_code c) (tau_env e) 0 (length (tau_env e)))
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
  move:h1.
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
  move:h1.
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


Lemma length_inv: forall e:environment, length e = Datatypes.length (tau_env e).
Proof.
  intros.
  induction e.
  done.
  Search "ective_pair".
  rewrite (surjective_pairing p).
  simpl.
  omega.
Qed.


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

Lemma correct_reduction_1: forall (c c0: code) (e s: environment), correct_state (cCons (Push c0) c,e,s) -> reduces (tau (cCons (Push c0) c,e,s)) (tau (c, e, cons (c0, e) s)).
Proof.
  intros.
  simpl.
  case s.
  simpl.
  apply sym.
  intros.
  destruct p.
  simpl in H.
  simpl.
  apply sym.
Qed.

Lemma correct_reduction_2: forall (c c0: code) (e e0 s: environment),correct_state ((cCons (Access 0) c, cons (c0,e0) e, s)) -> reduces (tau (cCons (Access 0) c, cons (c0,e0) e, s)) (tau (c0, e0, s)).
Proof.
  simpl.
  intros.
  case s.
  apply sym.
  intros.
  apply sym.
Qed.  
  
Lemma correct_reduction_3: forall (c c0: code) (e e0 s: environment) (n: nat), (n > 0) -> correct_state (cCons (Access n) c, cons (c0,e0) e, s) -> reduces (tau (cCons (Access n) c, cons (c0,e0) e, s)) (tau (exec_inst (cCons (Access n) c, cons (c0,e0) e, s))).
Proof.
  have h0:forall n, (beq_nat n n = true).
  intro.
  apply beq_nat_true_iff.
  reflexivity.
  unfold exec_inst.
  intros c c0 e e0 s n.
  case n.
  omega.
  intros.
  move : H0.

(*trial*)




(* good *)


  case s.
  case e.
  simpl.


  

  intros.
  destruct H0 as [[h1 [h2 h3]] [h4 h5]].
  omega.
  
  intros.
  move:H0.
  unfold tau.
  Search _(_ - S _).
  rewrite NPeano.Nat.sub_succ.
  Search _(_ - 0).
  rewrite -minus_n_O.
  rewrite (surjective_pairing p).
  intros.
  simpl.
  simpl in H0.
  rewrite -length_inv.
  destruct H0 as [[h1 [h2 h3]] [h4 h5]].
  have: n0 <= length e1.
  omega.
  intro.
  Search "leb_iff".
  apply leb_iff in x.
  rewrite -minus_n_O.
  rewrite ?x.
 
  rewrite ?h0.
  rewrite -minus_n_O.
  apply sym.

  intros.
  rewrite (surjective_pairing p).
  unfold tau.
  rewrite NPeano.Nat.sub_succ.
  rewrite -minus_n_O.
  rewrite -length_inv.
  rewrite -length_inv.
  unfold tau_code.
  unfold multiple_substitution.
  simpl in H0.
  destruct H0 as [[h1 [h2 h3]] [h4 h5]].
  have: n0 <= length e - 1.
  omega.
  intro.
  rewrite ?plus_O_n.
  have: S n0 <= length (cons (c0,e0) e) - 1.
  simpl.
  omega.
  intro.
  apply leb_iff in x.
  rewrite ?x.
  apply leb_iff in x0.
  rewrite x0.
  have: 0 <= n0.
  omega.
  intro.
  apply leb_iff in x1.
  rewrite x1.
  Search "andb".
  have: 0 <= S n0.
  omega.
  intro.
  apply leb_iff in x2.
  rewrite x2.
  simpl.
  rewrite ?h0.
  rewrite -minus_n_O.
  apply sym.
Qed.

Lemma correct_reduction_4: forall (c c0: code) (e e0 s: environment), correct_state (cCons Grab c, e, cons (c0,e0) s) -> reduces (tau (cCons Grab c, e, cons (c0,e0) s)) (tau (c, cons (c0,e0) e, s)).
Proof.
  intros.
  simpl in H.
  destruct H as [h0 [h1 h2]].
  destruct h1.
  destruct H0.
  case s.
  unfold tau.
  unfold tau_code.
  fold tau_code.
  unfold transform_stk.
  fold tau.
  simpl.
  
  rewrite red_equivalence.
  exists 1.
  simpl.
  exists (substitution 0 (multiple_substitution (tau_code c) (lift_all 1 0 (tau_env e)) 1
                (Datatypes.length (tau_env e))) (multiple_substitution (tau_code c0) (tau_env e0) 0
             (Datatypes.length (tau_env e0)))).
  split.
  Search "removeLamb".
  apply removeLamb.
  
  rewrite mult_sub_inv.
  admit.
  admit.
  admit.


  (*
  case s.
  simpl in H.
  destruct H as [h0 [h1 h2]].
  destruct h1.
  destruct H0.
  simpl.
  rewrite red_equivalence.
  exists 1.
  simpl.
  exists (substitution 0 (multiple_substitution (tau_code c) (lift_all 1 0 (tau_env e)) 1
                (Datatypes.length (tau_env e))) (multiple_substitution (tau_code c0) (tau_env e0) 0
             (Datatypes.length (tau_env e0)))).
  split.
  apply removeLamb.
  rewrite mult_sub_inv.
  admit.
  admit.
  admit.*)
Qed.
(*Lemma toy: forall (i: inst) (c: code) (e b: environment), reduces (tau (c, e, b)) (tau (exec_inst (c, e, b))) <-> reduces (tau (cCons i c, e, b)) (tau (exec_inst (cCons i c, e, b))).
Proof.
  split.
  case i.
  move: c e b.
  intros c e b n.
  move: c e b.
  induction n.
  intros c e b.
  case e.
  intro.
  apply sym.
  intros.
  destruct p.
  apply sym.
  intros c e b.
  case e.
  intros.
  apply sym.
  intros.
  destruct p.
  unfold exec_inst.
  apply sym.
  simpl.  
  simpl.
*)
  
Theorem correct_confluence: forall s: state, correct_state s -> reduces (tau s) (tau (exec_inst s)).
Proof.
  intro s.
  destruct s as ((c, e), s).
  move: e s.
  induction c.
  intros.
  apply sym.
  case i.
  intros n e s.
  case n.
  intros.
  unfold exec_inst.
  move:H.
  case e.
  intro.
  apply sym.
  intros.
  rewrite (surjective_pairing p).
  apply correct_reduction_2.
  rewrite -(surjective_pairing p).
  done.

  case e.
  intros.
  unfold exec_inst.
  apply sym.
  intros p e0 n0.
  rewrite (surjective_pairing p).
  intro.
  apply correct_reduction_3.
  omega.
  done.


  unfold exec_inst.
  intros.
  move:H.
  case s.
  intro.
  apply sym.
  intros.
  rewrite (surjective_pairing p).
  apply correct_reduction_4.
  rewrite -(surjective_pairing p).
  done.

  unfold exec_inst.
  intros.
  apply correct_reduction_1.
  done.
Qed.


 
  (*Unify every transition*)










  
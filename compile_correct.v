Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.
Require Import untypedLambda.
Require Import substitution.
Require Import reduction.
Require Import krivineAM.
Require Import compiler.

(*Division of the general result*)
Lemma transition_inv_access0: forall (c c0: code) (e e0 stack: environment), correct_state ((cCons (Access 0) c, cons c0 e0 e, stack)) -> correct_state  (c0, e0, stack).
Proof.
  simpl.
  intros.
  split.
  destruct H.
  inversion H; trivial.
  split.
  apply H.
  destruct H.
  inversion H; trivial.
Qed.

Lemma transition_inv_accessN: forall (c c0: code) (e e0 stack: environment) (n: nat), (n > 0) -> correct_state (cCons (Access n) c, cons c0 e0 e, stack) -> correct_state (cCons (Access (n-1)) c, e, stack).
Proof.
  simpl.
  intros.
  split.
  destruct H0.
  inversion H0; trivial.
  split.
  apply H0.
  destruct H0 as [h0 [h1 h2]].
  omega.
Qed.

Lemma transition_inv_push: forall (c c0: code) (e stack: environment), correct_state (cCons (Push c) c0, e, stack) -> correct_state (c0, e, cons c e stack).
Proof.
  simpl.  
  intros.
  destruct H as [h1 [h2 [h3 h4]]].
  split; trivial.
  split.
  apply Correct_stk.
  done.
  done.
  done.
  done.
Qed.

Lemma transition_inv_grab: forall (c c0: code) (e e0 stack: environment), correct_state (cCons Grab c, e, cons c0 e0 stack) -> correct_state (c, cons c0 e0 e, stack).
Proof.
  simpl.
  intros.
  destruct H as [h1 [h2 h3]].
  split.
  apply Correct_stk.
  inversion h2.
  done.
  by (inversion h2).
  trivial.
  split.
  by (inversion h2).
  by rewrite plus_comm in h3.
Qed.

(*Question 5.3*)
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
  intros c0 e1 e2.
  unfold exec_inst.
  case n.
  apply transition_inv_access0.
  intro.
  apply transition_inv_accessN.
  omega.
  unfold exec_inst.
  intros e e0.
  case e.
  done.
  intros c0 e1 e2.
  apply transition_inv_grab.
  intros c0 e e0.
  apply transition_inv_push.
Qed.


Lemma correct_reduction_access0: forall (c c0: code) (e e0 s: environment),correct_state ((cCons (Access 0) c, cons c0 e0 e, s)) -> (tau (cCons (Access 0) c, cons c0 e0 e, s)) = (tau (c0, e0, s)) \/ reducesInOneTo (tau (cCons (Access 0) c, cons c0 e0 e, s)) (tau (c0, e0, s)).
Proof.
  simpl.
  intros.
  case s.
  by left.
  intros.
  by left.
Qed.  

  
Lemma correct_reduction_accessN: forall (c c0: code) (e e0 s: environment) (n: nat), (n > 0) -> correct_state (cCons (Access n) c, cons c0 e0 e, s) -> (tau (cCons (Access n) c, cons c0 e0 e, s)) = (tau (exec_inst (cCons (Access n) c, cons c0 e0 e, s))) \/ reducesInOneTo (tau (cCons (Access n) c, cons c0 e0 e, s)) (tau (exec_inst (cCons (Access n) c, cons c0 e0 e, s))).
Proof.
  have:forall n:nat, beq_nat n n = true.
  intro.
  rewrite beq_nat_true_iff.
  reflexivity.
  intro h0.  
  unfold correct_state.
  intros c c0 e e0 s n.
  induction n.
  omega.
  intros.
  unfold exec_inst.
  destruct H0 as [h1 [h2 h3]].
  move:h1 h2 h3.
  case s.
  intros h1 h2 h3.
  simpl.
  rewrite ?h0.
  rewrite -?(length_inv).
  simpl in h3.
  rewrite -?minus_n_O.
  have:(leb n (lenEnv e - 1) = true).
  apply leb_iff.
  omega.
  intro h4.
  rewrite h4.
  have:(lenEnv e > 0).
  omega.
  intro.
  have:(exists n0:nat, lenEnv e = S n0).
  exists (lenEnv e - 1).
  omega.
  intro.
  case:x0.
  intros.
  rewrite p.
  have:(leb n x0 = true).
  apply leb_iff.
  omega.
  intro.
  rewrite x1.
  by left.
  intros.
  unfold tau.
  rewrite NPeano.Nat.sub_succ.
  rewrite -minus_n_O.
  rewrite -?length_inv.
  unfold tau_code.
  unfold multiple_substitution.
  rewrite -?minus_n_O.
  have:forall n: nat, 0 + n = n.
  intro.
  omega.
  intro.
  rewrite ?x.
  simpl in h3.
  have: S n <= lenEnv (cons c0 e0 e) - 1.
  simpl.
  simpl in h3.
  rewrite -minus_n_O.
  omega.
  intro.
  apply leb_iff in x0.
  rewrite length_inv in x0.
  rewrite x0.
  have: leb 0 (S n) = true.
  apply leb_iff.
  omega.
  intro.
  rewrite x1.
  have: leb 0 n = true.
  apply leb_iff.
  omega.
  intro.
  rewrite x2.
  have:(leb n (lenEnv e - 1) = true).
  apply leb_iff.
  omega.
  intro.
  rewrite length_inv in x3.
  rewrite x3.
  simpl.
  rewrite ?h0.
  by left.
Qed.

(*VERY USEFUL RESULTS TO PROVE THE LAST CASE*)
Lemma correct_reduction_push: forall (c c0: code) (e s: environment), correct_state (cCons (Push c0) c,e,s) -> ((tau (cCons (Push c0) c,e,s)) = (tau (c, e, cons c0 e s)) \/reducesInOneTo (tau (cCons (Push c0) c,e,s)) (tau (c, e, cons c0 e s))).
Proof.
  intros.
  simpl.
  case s.
  simpl.
  by left.
  intros.
  simpl in H.
  simpl.
  by left.
Qed.


Definition c_list_i (i:nat) (lu: list term) : Prop :=
  forall k: nat, k < Datatypes.length lu -> C i (nth k lu (Var 0)).

Fixpoint closed_list (i:nat) (lu: list term): Prop :=
  match lu with
    | nil => True
    | x :: xs => C i x /\ closed_list i xs
  end.

Lemma closed_list_eq: forall (lu: list term) (i: nat), closed_list i lu <-> c_list_i i lu.
Proof.
  induction lu.
  simpl.
  unfold c_list_i.
  split.
  simpl.
  intros.
  omega.
  done.
  simpl.
  split.
  intros.
  unfold c_list_i.
  intro.
  case k.
  simpl.
  intros.
  tauto.
  simpl.
  intros.
  apply IHlu.
  tauto.
  omega.
  intro.
  split.
  unfold c_list_i in H.
  apply (H 0).
  simpl.
  omega.
  apply IHlu.
  unfold c_list_i.
  intro.
  case k.
  intro.
  apply (H 1).
  simpl.
  omega.
  intros.
  apply (H (S (S n))).
  simpl.
  omega.
Qed.

Lemma lift_len_inv: forall (lu: list term) (i k: nat), length lu = length (lift_all i k lu).
Proof.
  induction lu; simpl.
  by simpl.
  intros.
  by rewrite -IHlu.
Qed.

Lemma remove_lift: forall (t: term) (i k: nat), C k t -> lifting i k t = t.
Proof.
  induction t; simpl.
  intros.
  have: leb k v = false.
  by apply leb_iff_conv.
  intros.
  by rewrite x.
  intros.
  rewrite -lambda_equivalence.
  by apply IHt.
  intros.
  rewrite app_equivalence.
  split.
  apply IHt1.
  tauto.
  apply IHt2.
  tauto.
Qed.


Lemma list_lift_free: forall (lu : list term) (i k : nat), c_list_i i lu -> c_list_i (i + 1) (lift_all 1 k lu).
Proof.
  induction lu; simpl.
  unfold c_list_i.
  simpl.
  intros.
  omega.
  unfold c_list_i.
  intros i k h1 k0.
  case k0.
  simpl.
  intro.
  apply lift_free.
  apply (h1 0).
  simpl.
  omega.
  simpl.  
  intros.
  apply IHlu.
  unfold c_list_i.
  intros.  
  apply (h1 (S k1)).
  simpl.
  omega.
  omega.
Qed.

Lemma mult_sub_clos: forall (t: term) (u: list term) (i: nat), closed_list i u -> C (i+Datatypes.length u) t -> C i (multiple_substitution i t u).
Proof.
  induction t.
  simpl.
  intros.
  have: beq_nat v v = true.
  apply beq_nat_true_iff.
  done.
  intro.
  rewrite x.
  have:leb v (i + Datatypes.length u - 1) = true.
  apply leb_iff.
  omega.
  intro.
  rewrite x0.
  rewrite Bool.andb_true_r.
  have:leb i v = false \/ leb i v = true.
  apply dic.
  intro.
  case x1.
  intro.
  rewrite H1.
  simpl.
  apply leb_iff_conv in H1.
  trivial.
  intro.
  rewrite H1.
  apply leb_iff in x0.
  apply leb_iff in H1.
  apply closed_list_eq in H.
  unfold c_list_i in H.
  apply H.
  omega.
  simpl.
  intros.
  apply (IHt (lift_all 1 0 u) (i+1)).
  apply closed_list_eq.
  apply closed_list_eq in H.  
  apply list_lift_free.
  done.
  rewrite -(lift_len_inv _ 1 0).
  have: i + Datatypes.length u + 1 = i + 1 + Datatypes.length u.
  omega.
  intro.
  rewrite -x.
  trivial.
  simpl.
  intros.
  split.
  apply IHt1.
  done.
  tauto.  
  apply IHt2.
  done.
  tauto.  
Qed.

Lemma closed_env: forall e:environment, correct_stk e -> closed_list 0 (tau_env e).
Proof.
  induction e.
  simpl.
  intros.
  trivial.
  intros.
  simpl.
  inversion H.
  split.
  apply mult_sub_clos.
  by apply IHe1.
  simpl.
  by rewrite -length_inv.
  by apply IHe2.
Qed.

Lemma remove_list_lift: forall lu: list term, closed_list 0 lu -> lift_all 1 0 lu = lu.
Proof.
  induction lu.
  by simpl.
  simpl.
  intros.
  have: lifting 1 0 a = a.
  apply remove_lift.
  tauto.
  intro.
  rewrite x.
  have: lift_all 1 0 lu = lu.
  apply IHlu.
  tauto.
  intro.
  by rewrite x0.
Qed.

Lemma fold_reduce: forall (s: environment) (t u: term), reducesInOneTo t u -> reducesInOneTo (fold_left (fun t1 t2 : term => App t1 t2) (transform_stk s) t) (fold_left (fun t1 t2 : term => App t1 t2) (transform_stk s) u).
Proof.
  induction s.
  intros t u.
  simpl.
  intro.
  trivial.
  intros.
  unfold transform_stk.
  fold transform_stk.
  have: match s2 with
        | nul => multiple_substitution 0 (tau_code c) (tau_env s1) :: nil
        | cons _ _ _ =>
            multiple_substitution 0 (tau_code c) (tau_env s1)
            :: transform_stk s2
        end = multiple_substitution 0 (tau_code c) (tau_env s1) :: match s2 with
        | nul => nil
        | cons _ _ _ => transform_stk s2
        end.
  by case s2.
  intro.
  rewrite x.
  clear x.
  have:forall t:term, (fold_left (fun t1 t2 : term => App t1 t2)
        (multiple_substitution 0 (tau_code c) (tau_env s1)
         :: match s2 with
            | nul => nil
            | cons _ _ _ => transform_stk s2
            end) t)
            =
            (fold_left (fun t1 t2 : term => App t1 t2)
                       match s2 with
                         | nul => nil
                         | cons _ _ _ => transform_stk s2
                       end) (App t (multiple_substitution 0 (tau_code c) (tau_env s1))).
  by case s2.
  intros.
  rewrite ?x.
  clear x.
  move:IHs2.
  case s2.
  simpl.
  intros.
  by apply appLeft.
  intros.
  apply IHs2.
  by apply appLeft.
Qed.

Lemma correct_reduction_grab: forall (c: code) (e s: environment), correct_state (cCons Grab c, e, s) -> (tau (cCons Grab c, e, s)) = (tau (exec_inst (cCons Grab c, e, s))) \/ reducesInOneTo (tau (cCons Grab c, e, s)) (tau (exec_inst (cCons Grab c, e, s))).
Proof.
  intros c e s.
  move: c e.
  induction s.
  simpl.
  intros.
  by left.
  intros.
  inversion H.
  unfold exec_inst.
  unfold tau.
  unfold tau_code.
  fold tau_code.
  unfold transform_stk.
  fold transform_stk.
  have: match s2 with
        | nul => multiple_substitution 0 (tau_code c) (tau_env s1) :: nil
        | cons _ _ _ =>
            multiple_substitution 0 (tau_code c) (tau_env s1)
            :: transform_stk s2
        end = multiple_substitution 0 (tau_code c) (tau_env s1) :: match s2 with
        | nul => nil
        | cons _ _ _ => transform_stk s2
        end.
  by case s2.
  intro.
  rewrite x.
  unfold multiple_substitution.
  fold multiple_substitution.
  simpl.
  rewrite mult_sub_inv.
  case s2.
  simpl.
  have:lift_all 1 0 (tau_env e) = tau_env e.
  apply remove_list_lift.
  by apply closed_env.
  clear x.
  intro.
  rewrite x.
  right.
  apply removeLamb.
  right.
  apply fold_reduce.
  simpl.  
  have:lift_all 1 0 (tau_env e) = tau_env e.
  apply remove_list_lift.
  by apply closed_env.
  clear x.
  intro.
  rewrite x.
  apply removeLamb.
  intro j.
  apply closed_list_eq.
  simpl in H.
  destruct H as [h1 [h2 h3]].
  by apply closed_env.  
Qed.

(*General case - Question 5.4*)
Theorem correct_reduction: forall s: state, correct_state s -> (tau s) = (tau (exec_inst s)) \/ reducesInOneTo (tau s) (tau (exec_inst s)).
Proof.
  intro s.
  destruct s as ((c, e), s).
  move: e s.
  induction c.
  intros.
  by left.
  case i.
  intros n e s.
  case n.
  intros.
  unfold exec_inst.
  move:H.
  case e.
  intro.
  by left.
  intros.
  apply correct_reduction_access0.
  done.
  case e.
  intros.
  unfold exec_inst.
  by left.
  intros c0 e0 e1 n0.
  intro.
  apply correct_reduction_accessN.
  omega.
  done.
  unfold exec_inst.
  intros.
  move:H.
  case s.
  intro.
  by left.
  intros.
  apply correct_reduction_grab.
  done.
  unfold exec_inst.
  intros.
  apply correct_reduction_push.
  done.
Qed.

(*Question 5.5*)
Lemma mult_exec_red: forall (s1 s2: state), mult_exec_inst s1 s2 -> correct_state s1 -> forall (t u:term), t = tau s1 -> u = tau s2 -> reduces t u.
Proof.
  intros s1 s2 h0 h1.
  induction h0.
  intros.
  rewrite H; rewrite H0.
  apply sym.
  intros.
  elim (correct_reduction s1).
  intro.
  rewrite H.
  rewrite H1.
  apply IHh0.
  apply correct_invariance; trivial.
  trivial.
  done.
  intro.
  apply (ind _ (tau (exec_inst s1)) _ ).
  rewrite H.
  done.
  apply IHh0.
    by apply correct_invariance.
    trivial.
    done.
    done.
Qed.

Lemma closed_implies_correct: forall t: term, C 0 t -> correct_state (compile t, nul, nul).
Proof.
  induction t; simpl.
  omega.
  intros.
  split.
  simpl.
  apply Correct_stk_nil.
  split.
  apply Correct_stk_nil.
  rewrite -tau_nil_env.
  have:(tau (compile t, nul, nul)) = t.
  apply invert_comp.
  intro.
    by rewrite x.
  intros; destruct H.
  split.
  apply Correct_stk_nil.
  split.
  apply Correct_stk_nil.
  split.
  rewrite -tau_nil_env.
  by rewrite invert_comp.
  rewrite -tau_nil_env.
  by rewrite invert_comp.
Qed.
    
Theorem compiling_correct: forall (t: term) (s: state), C 0 t -> mult_exec_inst (compile t, nul, nul) s -> reduces t (tau s).
Proof.
  intros.
  apply (mult_exec_red (compile t, nul, nul) s).
  done.
  by apply closed_implies_correct.
  symmetry.
  apply invert_comp.
  done.
Qed.
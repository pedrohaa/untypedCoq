Require Import ssreflect Arith.
Require Import Arith.EqNat.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Omega.
Require Import untypedLambda.
Require Import substitution.
Require Import krivineAM.

(*Compiler function - Fourth & Fifth Part*)
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

Fixpoint tau_env (e: environment): list term :=
  match e with
    | nul => nil
    | cons c0 e0 e1 =>
      (multiple_substitution 0 (tau_code c0) (tau_env e0)) :: tau_env e1
  end.

Fixpoint transform_stk (stk: environment): list term :=
  match stk with
      | cons c0 e0 nul => multiple_substitution 0 (tau_code c0) (tau_env e0) :: nil
      | cons c0 e0 e1 => (multiple_substitution 0 (tau_code c0) (tau_env e0)) :: (transform_stk e1)
      | nul => nil
  end.

Fixpoint tau (s: state): term :=
  match s with
    | (c, e, stk) =>
      match stk with
        | nul => multiple_substitution 0 (tau_code c) (tau_env e)
        | stk => fold_left (fun t1 t2 => App t1 t2) (transform_stk stk) (multiple_substitution 0 (tau_code c) (tau_env e))
      end
  end.


Fixpoint lenEnv (e: environment): nat :=
  match e with
    | nul => 0
    | cons c0 e0 e1 => 1 + (lenEnv e1)
  end.


Lemma length_inv: forall e:environment, lenEnv e = length (tau_env e).
Proof.
  intros.
  induction e.
  done.
  simpl.
  omega.
Qed.


Inductive correct_stk : environment -> Prop :=
| Correct_stk_nil : correct_stk nul
| Correct_stk : forall (c0: code) (e0 e: environment),
                  C (lenEnv e0) (tau_code c0) -> correct_stk e0 -> correct_stk e ->
                  correct_stk (cons c0 e0 e).

Definition correct_state (s: state): Prop:=
  match s with
   | (c, e, stk) => (correct_stk e) /\ (correct_stk stk) /\ (C (lenEnv e) (tau_code c))
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

(*Question 5.2*)
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

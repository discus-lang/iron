
Require Export Iron.Language.SimpleDelayed.SubstXX.
Require Import Iron.Language.SimpleDelayed.Preservation.
Require Import Iron.Language.SimpleDelayed.TypeX.
Require Export Iron.Language.SimpleDelayed.Step.
Require Export Iron.Language.SimpleDelayed.Exp.


(********************************************************************)
(** Big Step Evaluation *)
(*  This is also called 'Natural Semantics'.
    It provides a relation between the expression to be reduced 
    and its final value. *)
Inductive Eval : exp -> exp -> Prop :=
 | EvDone
   :  forall x
   ,  Done   x
   -> Eval   x x

 | EvLamApp
   :  forall bs n t11 x1 x12 x2 v2 v3
   ,  Eval x1 (XLam bs n t11 x12) 
   -> Eval x2 v2 
   -> Eval (substXX (BBind n t11 v2 :: bs) x12) v3
   -> Eval (XApp x1 x2) v3.
Hint Constructors Eval.


(* Invert all hypothesis that are compound eval statements. *)
Ltac inverts_eval :=
 repeat 
  (match goal with 
   | [ H: Eval (XApp _ _)_ |- _ ] => inverts H
   end).


(* A terminating big-step evaluation always produces a whnf.
   The fact that the evaluation terminated is implied by the fact
   that we have a finite proof of EVAL to pass to this lemma. *)
Lemma eval_produces_done
 :  forall x1 v1
 ,  Eval   x1 v1
 -> Done   v1.
Proof.
 intros. induction H; eauto.
Qed.
Hint Resolve eval_produces_done.


Lemma steps_trans
 :  forall x1 x2 x3
 ,  Steps x1 x2 -> Steps x2 x3
 -> Steps x1 x3.
Proof.
 intros. induction H; intros.
 auto.
 eapply EsAppend. eapply H. auto.
 eapply EsAppend. eapply H. eapply IHSteps. trivial.
Qed.


(********************************************************************)
(** * Big to Small steps *)
(* Convert a big-step evaluation into a list of individual
   machine steps. *)
Lemma steps_of_eval
 :  forall te x1 t1 x2
 ,  TypeX  te x1 t1
 -> Eval   x1 x2
 -> Steps  x1 x2.
Proof.
 intros te x1 t1 v2 HT HE. gen te t1.

 (* Induction over the form of (EVAL x1 x2) *)
 induction HE; intros.
 Case "EVDone".
  apply EsNone.

 Case "EVLamApp".
  inverts_type.

  lets S1: IHHE1 H2. clear IHHE1.
  lets T1: preservation_steps H2 S1.

  lets S2: IHHE2 H4. clear IHHE2.
  lets T2: preservation_steps H4 S2.

  inverts keep T1.
  simpl in H9.
  have ( (te ><  map stripB bs) :> SSig n t0
       =  te >< (map stripB bs  :> SSig n t0)) as D1.
  rewrite D1 in H9. clear D1.

  have ( map stripB bs :> SSig n t0
       = map stripB (bs :> BBind n t0 v2)) as D2.
  rewrite D2 in H9. clear D2.

  eapply subst_exp_exp in H9; eauto.
  lets S3: IHHE3 H9.
  clear IHHE3.
  lets T3: preservation_steps H9 S3.

  lets P1: steps_context XcApp1 S1.
  eapply steps_trans. eapply P1. clear P1.

  have (Done (XLam bs n t0 x12)) as HH.
  lets P2: steps_context XcApp2 S2. eapply HH.
  eapply steps_trans. eapply P2. clear P2.

  eapply EsAppend.
  eapply EsLamApp. eauto. auto.
Qed.


(********************************************************************)
(** * Small to Big steps *)
(** Convert a list of individual machine steps to a big-step
    evaluation. The main part of this is the expansion lemma, which 
    we use to build up the overall big-step evaluation one small-step
    at a time. The other lemmas are used to feed it small-steps.
 *)

(* Given an existing big-step evalution, we can produce a new one
   that does an extra step before returning the original value.
 *)
Lemma eval_expansion
 :  forall te x1 t1 x2 v3
 ,  TypeX  te x1 t1
 -> Step   x1 x2 -> Eval x2 v3 
 -> Eval   x1 v3.
Proof.
 intros te x1 t1 x2 v3 HT HS HE. gen te t1 v3.
 induction HS; intros.

 Case "context".
  destruct H; inverts_type; inverts_eval; eauto.

  admit. admit.


 Case "application".
  inverts_type.
  eapply EvLamApp; eauto.
  admit.
Admitted.


(* Convert a list of small steps to a big-step evaluation. *)
Lemma eval_of_stepsl
 :  forall te x1 t1 v2
 ,  TypeX  te x1 t1
 -> StepsL x1 v2 -> Done v2
 -> Eval   x1 v2.
Proof.
 intros te x1 t1 v2 HT HS Hv.
 induction HS; try burn.

 eapply eval_expansion;
  eauto using preservation.
Qed.


(* Convert a multi-step evaluation to a big-step evaluation.
   We use stepsl_of_steps to flatten out the append constructors
   in the multi-step evaluation, leaving a list of individual
   small-steps. *)
Lemma eval_of_steps
 :  forall te x1 t1 v2
 ,  TypeX  te x1 t1
 -> Steps  x1 v2 -> Done v2
 -> Eval   x1 v2.
Proof.
 intros.
 eapply eval_of_stepsl; eauto.
  apply stepsl_of_steps; auto.
Qed.


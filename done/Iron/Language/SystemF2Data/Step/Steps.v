
Require Export Iron.Language.SystemF2Data.Exp.
Require Export Iron.Language.SystemF2Data.Step.Context.
Require Export Iron.Language.SystemF2Data.Step.Step.

(********************************************************************)
(* Multi-step evaluation
   A sequence of small step transitions.

   As opposed to STEPSL, this version has an append constructor
   EsAppend that makes it easy to join two evaluations together.
   We use this when converting big-step evaluations to small-step. *)
Inductive STEPS : exp -> exp -> Prop :=

 (* After no steps, we get the same exp.
    We need this constructor to match the EVDone constructor
    in the big-step evaluation, so we can convert between big-step
    and multi-step evaluations. *)
 | EsNone
   :  forall x1
   ,  STEPS x1 x1

 (* Take a single step. *)
 | EsStep
   :  forall x1 x2
   ,  STEP  x1 x2
   -> STEPS x1 x2

 (* Combine two evaluations into a third. *)
 | EsAppend
   :  forall x1 x2 x3
   ,  STEPS x1 x2 -> STEPS x2 x3
   -> STEPS x1 x3.

Hint Constructors STEPS.


(********************************************************************)
(* Multi-step evaluating a wnf doesn't change it. *)
Lemma steps_wnfX 
 :  forall x v
 ,  wnfX x -> STEPS x v -> v = x.
Proof.
 intros x v HW HS.
 induction HS; auto.
  Case "EsStep".
   apply step_wnfX; auto.
  
  Case "EsAppend".
   have (x2 = x1).
   subst. auto.
Qed.


(********************************************************************)
(* Multi-step evaluation in a context. *)
Lemma steps_context
 :  forall C x1 x1'
 ,  exp_ctx C
 -> STEPS x1 x1'
 -> STEPS (C x1) (C x1').
Proof.
 intros C x1 x1' HC HS.
 induction HS; eauto.
Qed.


(********************************************************************)
(* Multi-step evaluation of a data constructor argument. *)
Lemma steps_context_XCon
 :  forall C x v dc ts
 ,  exps_ctx wnfX C
 -> STEPS x v
 -> STEPS (XCon dc ts (C x)) (XCon dc ts (C v)).
Proof.
 intros C x v dc ts HC HS.
 induction HS; auto.
 - lets D: EsContext XcCon; eauto. 
 - eauto.
Qed.


Lemma steps_in_XCon
 :  forall xs ts vs dc
 ,  Forall2 STEPS xs vs
 -> Forall wnfX vs
 -> STEPS (XCon dc ts xs) (XCon dc ts vs).
Proof.
 intros xs ts vs dc HS HW.
 lets HC: make_chain HS HW.
 - eapply steps_wnfX.
 - clear HS. clear HW.
   induction HC; auto.
   eapply (EsAppend (XCon dc ts (C x)) (XCon dc ts (C v))); auto.
   eapply steps_context_XCon; auto.
Qed.


(********************************************************************)
(* Multi-step evaluation of a primitive operator argument. *)
Lemma steps_context_XPrim
 :  forall C x v p
 ,  exps_ctx wnfX C
 -> STEPS x v
 -> STEPS (XPrim p (C x)) (XPrim p (C v)).
Proof.
 intros C x v p HC HS.
 induction HS; auto.
 - lets D: EsContext XcPrim; eauto.
 - eauto.
Qed.


Lemma steps_in_XPrim
 :  forall xs vs p
 ,  Forall2 STEPS xs vs
 -> Forall wnfX vs
 -> STEPS (XPrim p xs) (XPrim p vs).
Proof.
 intros xs vs p HS HW.
 lets HC: make_chain HS HW.
 - eapply steps_wnfX.
 - clear HS. clear HW.
   induction HC; auto.
   eapply (EsAppend (XPrim p (C x)) (XPrim p (C v))); auto.
   eapply steps_context_XPrim; auto.
Qed.



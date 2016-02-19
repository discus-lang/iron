
Require Export Iron.Language.SimpleDelayed.TypeX.
Require Export Iron.Language.SimpleDelayed.SubstXX.


(*******************************************************************)
(* Small Step evaluation *)
Inductive Step : exp -> exp -> Prop :=

 (* Evaluation in a context. *)
 | EsAppLeft 
   :  forall x1 x1' x2
   ,  Step  x1 x1'
   -> Step (XApp x1 x2) (XApp x1' x2)

 | EsAppRight
   :  forall x1 x2 x2'
   ,  Value x1
   -> Step  x2 x2'
   -> Step (XApp x1 x2) (XApp x1 x2')

 (* Function application. *)
 | EsAbsApp 
   :  forall bs1 n1 t1 x1 v2
   ,  Done v2
   -> Step (XApp (XAbs bs1 n1 t1 x1) v2)
           (substXX (BBind n1 t1 v2 :: bs1) x1).

Hint Constructors Step.


(********************************************************************)
(* Multi-step evaluation
   A sequence of small step transitions.
   As opposed to StepsL, this version has an append constructor
   EsAppend that makes it easy to join two evaluations together.
   We use this when converting big-step evaluations to small-step. *)
Inductive Steps : exp -> exp -> Prop :=

 (* After no steps, we get the same exp.
    We need this constructor to match the EVDone constructor
    in the big-step evaluation, so we can convert between big-step
    and multi-step evaluations. *)
 | EsNone
   :  forall x1
   ,  Steps x1 x1

 (* Take a single step. *)
 | EsStep
   :  forall x1 x2
   ,  Step  x1 x2
   -> Steps x1 x2

 (* Combine two evaluations into a third. *)
 | EsAppend
   :  forall x1 x2 x3
   ,  Step  x1 x2 -> Steps x2 x3
   -> Steps x1 x3.

Hint Constructors Steps.


(* Multi-step evaluation on the left of an application. *)
Lemma steps_context_left
 :  forall x1 x1' x2
 ,  Steps x1  x1'
 -> Steps (XApp x1 x2) (XApp x1' x2).
Proof.
 intros x1 x1' x2 HS.
 induction HS; eauto.
Qed.


(* Multi-step evaluation on the right of an application. *)
Lemma steps_context_right
 :  forall bs n t x1 x2 x2'
 ,  Steps x2 x2'
 -> Steps (XApp (XAbs bs n t x1) x2)
          (XApp (XAbs bs n t x1) x2').
Proof.
 intros bs n t x1 x2 x2' HS.
 induction HS; eauto.
Qed.


(********************************************************************)
(* Left linearised multi-step evaluation
   As opposed to STEPS, this version provides a single step at a time
   and does not have an append constructor. This is convenient
   when converting a small-step evaluations to big-step, via the
   eval_expansion lemma.*)
Inductive StepsL : exp -> exp -> Prop :=
 | EslNone 
   : forall x1
   , StepsL x1 x1

 | EslCons
   :  forall x1 x2 x3
   ,  Step   x1 x2 -> StepsL x2 x3 
   -> StepsL x1 x3.

Hint Constructors StepsL.


(* Transitivity of left linearised multi-step evaluation.
   We use this when "flattening" a big step evaluation to the
   small step one. *)
Lemma stepsl_trans
 :  forall x1 x2 x3
 ,  StepsL x1 x2 -> StepsL x2 x3
 -> StepsL x1 x3.
Proof.
 intros x1 x2 x3 HS1 HS2.
 induction HS1; eauto.
Qed.


(* Linearise a regular multi-step evaluation.
   This flattens out all the append constructors, leaving us with
   a list of individual transitions. *)
Lemma stepsl_of_steps
 :  forall x1 x2
 ,  Steps  x1 x2
 -> StepsL x1 x2.
Proof. 
 intros x1 x2 HS.
 induction HS; eauto using stepsl_trans.
Qed.



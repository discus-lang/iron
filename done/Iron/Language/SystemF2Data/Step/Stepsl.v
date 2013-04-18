
Require Export Iron.Language.SystemF2Data.Exp.
Require Export Iron.Language.SystemF2Data.Step.Context.
Require Export Iron.Language.SystemF2Data.Step.Step.
Require Export Iron.Language.SystemF2Data.Step.Steps.


(* Left linearised multi-step evaluation
   As opposed to STEPS, this version provides a single step at a time
   and does not have an append constructor. This is convenient
   when converting a small-step evaluations to big-step, via the
   eval_expansion lemma. *)
Inductive STEPSL : exp -> exp -> Prop :=
 | EslNone 
   : forall x1
   , STEPSL x1 x1

 | EslCons
   :  forall x1 x2 x3
   ,  STEP   x1 x2 -> STEPSL x2 x3 
   -> STEPSL x1 x3.

Hint Constructors STEPSL.


(* Transitivity of left linearised multi-step evaluation.
   We use this when "flattening" a big step evaluation to the
   small step one. *)
Lemma stepsl_trans
 :  forall x1 x2 x3
 ,  STEPSL x1 x2 -> STEPSL x2 x3
 -> STEPSL x1 x3.
Proof.
 intros x1 x2 x3 H1 H2.
 induction H1; eauto.
Qed.


(* Linearise a regular multi-step evaluation.
   This flattens out all the append constructors, leaving us with
   a list of individual transitions. *)
Lemma stepsl_of_steps
 :  forall x1 x2
 ,  STEPS  x1 x2
 -> STEPSL x1 x2.
Proof. 
 intros x1 x2 HS.
 induction HS; 
  eauto using stepsl_trans.
Qed.

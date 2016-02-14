
Require Export Iron.Language.SimpleDelayed.SubstXX.
Require Export Iron.Language.SimpleDelayed.Exp.


Definition isXLam (x1: exp): Prop := 
 (exists bs n t x, x1 = XLam bs n t x).


Lemma isXLam_true
 : forall bs n t x, isXLam (XLam bs n t x).
Proof.
 intros.
 unfold isXLam.
 exists bs. exists n. exists t. exists x.
 trivial.
Qed.
Hint Resolve isXLam_true.

Lemma isXLam_XVar
 : forall n
 , ~isXLam (XVar n).
Proof. 
 intros. intuition. nope.
Qed.
Hint Resolve isXLam_XVar.


Lemma isXLam_XApp
 : forall x1 x2
 , ~isXLam (XApp x1 x2).
Proof.
 intros. intuition. nope.
Qed.
Hint Resolve isXLam_XApp.


Inductive Done : exp -> Prop :=
 | DoneVar 
   :  forall n
   ,  Done (XVar n)

 | DoneLam 
   :  forall bs n t x
   ,  Done (XLam bs n t x)

 | DoneApp 
   :  forall x1 x2
   ,  Done x1 /\ ~isXLam x1
   -> Done (XApp x1 x2).



(*******************************************************************)
(* Evaluation contexts for expressions.
   An evaluation context is an expression with a hole in any place
   that can take a step via our evaluatio rules. We represent
   the hole by the function that fills it. *)
Inductive exp_ctx : (exp -> exp) -> Prop :=
 | XcApp1
   :  forall x2
   ,  exp_ctx (fun xx => XApp xx x2)

 | XcApp2 
   :  forall v1
   ,  Done v1 
   -> exp_ctx (fun xx => XApp v1 xx).

Hint Constructors exp_ctx.


(* Small Step evaluation *)
Inductive Step : exp -> exp -> Prop :=

 (* Evaluation in a context. *)
 | EsContext 
   :  forall C x x'
   ,  exp_ctx C
   -> Step x x'
   -> Step (C x) (C x')

 (* Function application. *)
 | EsLamApp 
   :  forall bs1 n1 t1 x1 v2
   ,  Done v2
   -> Step (XApp (XLam bs1 n1 t1 x1) v2)
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


(* Multi-step evaluation in a context.
   If an expression can be evaluated at top level, then it can 
   be evaluated to the same result in any evaluation context. *)
Lemma steps_context
 :  forall C x1 x1'
 ,  exp_ctx C
 -> Steps x1 x1'
 -> Steps (C x1) (C x1').
Proof.
 intros C x1 x1' HC HS.
 induction HS; burn.
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
 induction HS1; burn.
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
 induction HS; burn using stepsl_trans.
Qed.



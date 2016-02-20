
Require Export Iron.Language.DelayedSimple.Progress.
Require Export Iron.Language.DelayedSimple.Preservation.


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

 | EvDoneApp
   :  forall x1 x1' x2
   ,  Eval x1 x1' 
   -> Done x1' -> not (Value x1')
   -> Eval (XApp x1 x2) (XApp x1' x2)

 | EvAbsApp
   :  forall ss v t11 x1 x12 x2 v2 v3
   ,  Eval x1 (XAbs ss v t11 x12) 
   -> Eval x2 v2 
   -> Eval (substXX (BBind v t11 v2 :: ss) x12) v3
   -> Eval (XApp x1 x2) v3.

Hint Constructors Eval.


(* Invert all hypothesis that are compound eval statements. *)
Ltac inverts_eval :=
 repeat 
  (match goal with 
   | [ H: Eval (XApp _ _)_ |- _ ] => inverts H
   end).


(* Evaluating a value produces a value. *)
Lemma eval_value
 :  forall v1 v2
 ,  Value  v1
 -> Eval   v1 v2 
 -> Value  v2.
Proof.
 intros v1 v2 HV HE.
 destruct HE.
 - assumption.
 - inverts HV.
 - inverts HV.
Qed.


(* A terminating big-step evaluation always produces a whnf.
   The fact that the evaluation terminated is implied by the fact
   that we have a finite proof of Eval to pass to this lemma. *)
Lemma eval_produces_done
 :  forall x1 v1
 ,  Eval   x1 v1
 -> Done   v1.
Proof.
 intros. induction H; eauto.
Qed.


Lemma steps_trans
 :  forall x1 x2 x3
 ,  Steps x1 x2 -> Steps x2 x3
 -> Steps x1 x3.
Proof.
 intros.
 induction H; intros.
 - assumption.
 - eapply EsAppend. eapply H. assumption.
 - eapply EsAppend. eapply H. eapply IHSteps. assumption.
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
 - Case "EvDone".
   apply EsNone.

 - Case "EvDoneApp".
   inverts_type.
   eapply steps_trans.
   + apply steps_context_left.
     eapply IHHE. eauto.

   + destruct x1'.
     * nope.
     * apply steps_context_right.
       nope.
     * nope.

 - Case "EvAbsApp".
   inverts_type.

   (* reduce the functional expression to a lambda. *)
   lets S1: IHHE1 H2. clear IHHE1.
   lets T1: preservation_steps H2 S1.
   eapply steps_trans.
   eapply steps_context_left.
   eapply S1.

   (* reduce the argument to a trivial expression. *)
   lets S2: IHHE2 H4. clear IHHE2.
   lets T2: preservation_steps H4 S2.
   eapply steps_trans.
   eapply steps_context_right.
   eapply S2.

   (* perform the substitution. *)
   eapply EsAppend.
   eapply EsAbsApp.
   eapply eval_produces_done.
   eauto.

   inverts_type.
   eapply IHHE3.
   eapply subst_exp_exp.

   assert ( (te ><  map stripB ss) :> SSig v t0
          =  te >< (map stripB ss  :> SSig v t0)) as D1; auto.
   rewrite stripS_fold in D1.
   rewrite D1 in H9. clear D1.
   simpl. eauto.

   unfold ForallSubstXT. simpl.
   eapply Forall2_cons; auto.
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
 :  forall te x1 t1 x2 x3
 ,  TypeX  te x1 t1
 -> Step   x1 x2 -> Eval x2 x3 
 -> Eval   x1 x3.
Proof.
 intros te x1 t1 x2 x3 HT HS HE. gen te t1 x3.
 induction HS; intros.

 - Case "functional expression steps.".
   inverts_type.
   lets E1: IHHS H2.

   inverts_eval.
   + inverts H.
     * nope.
     * rip.
   + rip.
   + eapply EvAbsApp; eauto.

 - Case "application".
   inverts_type.
   inverts_eval.

   + inverts H.
     inverts_done.
     nope. rip.
     assert (Value (XAbs ss v t x)).
      auto. nope.

   + assert (Value x1').
      eapply eval_value; eauto.
     nope.

   + eapply EvAbsApp; eauto.

 - Case "application".
   inverts_type.
   eapply EvAbsApp; eauto.
Qed.


(* Convert a list of small steps to a big-step evaluation. *)
Lemma eval_of_stepsl
 :  forall te x1 t1 v2
 ,  TypeX  te x1 t1
 -> StepsL x1 v2 -> Done v2
 -> Eval   x1 v2.
Proof.
 intros te x1 t1 v2 HT HS Hv.
 induction HS; eauto.

 eapply eval_expansion; eauto.
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


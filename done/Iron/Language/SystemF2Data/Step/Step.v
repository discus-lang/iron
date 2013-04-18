
Require Export Iron.Language.SystemF2Data.Exp.
Require Export Iron.Language.SystemF2Data.Step.Context.


(** * Single Small Step Evaluation *)
(** The single step rules model the individual transitions that the 
     machine can make at runtime. *)

Inductive STEP : exp -> exp -> Prop :=

 (* Step some sub-expression in an evaluation context *)
 | EsContext 
   :  forall C x x'
   ,  exp_ctx C
   -> STEP x x'
   -> STEP (C x) (C x')

 | EsLamApp
   : forall t11 x12 v2
   ,  wnfX v2
   -> STEP (XApp   (XLam t11 x12) v2)
           (substXX 0 v2 x12)

 (* type applications *)
 | EsLAMAPP
   :  forall x12 t2      
   ,  STEP (XAPP (XLAM x12) t2)
           (substTX 0 t2 x12)

 | EsCaseAlt
   :  forall dc ts vs alts x
   ,  Forall wnfX vs
   -> getAlt dc alts = Some (AAlt dc x)
   -> STEP (XCase (XCon dc ts vs) alts)
           (substXXs 0 vs x).

Hint Constructors STEP.


(* Stepping a wnf doesn't change it. *)
Lemma step_wnfX
 :  forall x v
 ,  wnfX x -> STEP x v -> v = x.
Proof.
 intros x v HW HS.
 induction HS; nope.
  destruct H; auto; nope.

 Case "XCon dc (C x)".
  inverts HW.
  assert (wnfX x).
  eapply exps_ctx_Forall; eauto.
  assert (x' = x); auto.
  subst. auto.
Qed.


Lemma step_context_XCon_exists
 :  forall  C x dc ts
 ,  exps_ctx wnfX C 
 -> (exists x', STEP x x')
 -> (exists x', STEP (XCon dc ts (C x)) (XCon dc ts (C x'))).
Proof.
 intros C x dc ts HC HS.
 shift x'.
 eapply (EsContext (fun xx => XCon dc ts (C xx))); auto.
Qed.




Require Import Iron.Language.SystemF2Data.Exp.
Require Import Iron.Language.SystemF2Data.Step.Step.
Require Import Iron.Language.SystemF2Data.Step.Steps.
Require Import Iron.Language.SystemF2Data.Step.Stepsl.


(********************************************************************)
(* When a well typed application of a primitive to some values
   transitions to the next state, then its type is preserved. 
   This tells us that the types given in the primitive definitions
   match their runtime behaviour. *)
Lemma preservation_prim
 :  forall ds p vsArg vResult t
 ,  Forall wnfX vsArg
 -> STEP (XPrim p vsArg) vResult
 -> TYPE ds nil nil (XPrim p vsArg) t
 -> TYPE ds nil nil vResult         t.
Proof.
 intros ds p vs vResult t HV HS HT.
 inverts HT.
 inverts HS.

 - inverts H0; nope.
   inverts H.
   have (wnfX x)
    by (eapply exps_ctx_Forall; eauto).
   eapply step_wnfX in H; eauto. subst.
   eauto.

 - destruct p. 
   + SCase "PAdd".
     simpl in H1.
     inverts H1. inverts H3. inverts H6.
     have (wnfX x). have (wnfX x0).
     eapply value_form_nat in H4; eauto. destruct H4 as [n1].
     eapply value_form_nat in H3; eauto. destruct H3 as [n2].
     subst. snorm.

   + SCase "PIsZero".
     simpl in H1.
     inverts H1. inverts H3. inverts H6.
     have (wnfX x).
     eapply value_form_nat in H4; eauto. destruct H4 as [n1].
     subst. snorm.
Qed.


(********************************************************************)
(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall ds x x' t
 ,  TYPE ds nil nil x  t
 -> STEP x x'
 -> TYPE ds nil nil x' t.
Proof.
 intros ds x x' t HT HS. gen t.
 induction HS; intros; inverts_type; eauto.

 (*************************************)
 - Case "EsContext".
   destruct H; inverts_type; eauto. 

  + SCase "XCon".
    eapply TYCon; eauto.
    eapply exps_ctx_Forall2_swap; eauto.

  + SCase "XPrim".
    eapply TYPrim; eauto.
    eapply exps_ctx_Forall2_swap; eauto.


 (*************************************)
 - Case "EsLamApp".
   eapply subst_exp_exp; eauto.


 (*************************************)
 - Case "EsLAMAPP".
   have HT: (TYPE ds nil (substTE 0 t2 nil) 
                         (substTX 0 t2 x12) (substTT 0 t2 t1))
    by (eapply subst_type_exp; eauto).
   snorm.


 (*************************************)
 - Case "EsCaseAlt".
   eapply subst_exp_exp_list; eauto.

   norm.
   have (In (AAlt dc x) alts).
   have HA: (TYPEA ds nil nil (AAlt dc x) (makeTApps (TCon tc) ts) t).
   inverts HA.
   rewrite H11 in H16. inverts H16.
   rewrite H15 in H10. inverts H10.

   have HTC: (getCtorOfType (TCon tc0) = Some tc0).
    erewrite getCtorOfType_makeTApps in H5; eauto.
   inverts H5.

   snorm.
   rewrite H6 in H15. inverts H15.
   have HTK1: (length ts      = length ks0).
   have HTK2: (length tsParam = length ks0).
   rewrite <- HTK1 in HTK2.
   have (tsParam = ts)
    by (eapply makeTApps_args_eq; eauto).
   subst.
   eauto.


 (*************************************)
 - Case "EsPrim".
   eapply preservation_prim; eauto.
Qed.


(* When we multi-step evaluate some expression,
   then the result has the same type as the original. *)  
Lemma preservation_steps
 :  forall ds x1 t1 x2
 ,  TYPE ds nil nil x1 t1
 -> STEPS       x1 x2
 -> TYPE ds nil nil x2 t1.
Proof.
 intros ds x1 t1 x2 HT HS.
 induction HS; eauto using preservation.
Qed.


(* When we multi-step evaluate some expression, 
   then the result has the same type as the original.
   Using the left-linearised form for the evaluation.
 *)
Lemma preservation_stepsl
 :  forall ds x1 t1 x2
 ,  TYPE ds nil nil x1 t1
 -> STEPSL x1 x2
 -> TYPE ds nil nil x2 t1.
Proof.
 intros ds x1 t1 x2 HT HSL.
 induction HSL; eauto using preservation.
Qed.


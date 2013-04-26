
Require Import Iron.Language.SystemF2Data.Exp.
Require Import Iron.Language.SystemF2Data.Step.Step.


(********************************************************************)
(* If we have a well typed case match on a data object then there
   is a case alternative corresponding to that data constructor *)
Lemma getAlt_has
 :  forall ds dc ts xs alts t
 ,  DEFSOK ds
 -> TYPE ds nil nil (XCase (XCon dc ts xs) alts) t
 -> (exists x, getAlt dc alts = Some (AAlt dc x)).
Proof.
 intros.
 eapply getAlt_exists.
 inverts_type.
 norm. 
 eapply H8.
 have (getCtorOfType (TCon tc) = Some tc) as HC.
 erewrite getCtorOfType_makeTApps in H5; eauto.
 inverts H5.
 eauto.
Qed.
Hint Resolve getAlt_has.


(* Well typed primitives applied to values can always progress. *)
Lemma progress_prim
 :  forall ds p tsArg tResult xs 
 ,  primDef p = DefPrim tsArg tResult
 -> Forall2 (TYPE ds nil nil) xs tsArg
 -> Forall  wnfX xs
 -> (exists x, STEP (XPrim p xs) x).
Proof.
 intros.
 destruct p.

 - Case "PAdd".
   snorm. inverts H.
   inverts H0. inverts H5. inverts H6.
   eapply value_form_nat in H4.
   + destruct H4 as [n]. subst.
     eapply value_form_nat in H3.
     * destruct H3 as [n']. subst.
       exists (XLit (LNat (n + n'))). 
       eauto.
     * have (closedX x0).
       eauto.
   + have (closedX x).
     eauto.

 - Case "PIsZero".
   snorm. inverts H.
   inverts H0. inverts H5.
   eapply value_form_nat in H4.
   + destruct H4 as [n]. subst.
     exists (XLit (LBool (beq_nat n 0))).
     eauto.
   + have (closedX x).
     eauto.
Qed. 
Hint Resolve progress_prim.


(********************************************************************)
(* A well typed expression is either a well formed value, 
   or can transition to the next state. *)
Theorem progress
 :  forall ds x t
 ,  DEFSOK ds
 -> TYPE ds nil nil x t
 -> value x \/ (exists x', STEP x x').
Proof.
 intros. gen t.
 induction x using exp_mutind with 
  (PA := fun a => a = a); 
   intros.

 (*************************************)
 - Case "XVar".
   (* Variables aren't values. *)
   nope.


 (*************************************)
 - Case "XLAM".
   (* Closed type abstractions are already values. *)
   left. apply type_wfX in H0. auto.


 (*************************************)
 - Case "XAPP".
   inverts keep H0.
   edestruct IHx. eauto.

   (* If the function part of a type application is a value then
      is can only step if it is a type abstraction. *)
   + SCase "x value".
     right. 
     inverts H1. 
     inverts H3; try nope.
     (* The function part is a type abstraction, 
        so we can do the substitution. *)
     * SSCase "x = XLAM". 
       exists (substTX 0 t2 x1). 
       eapply EsLAMAPP.

     (* Can't happen, fully applied data constructors never have
        quantified types. *)
     * SSCase "x = XCon".
       inverts_type.
       have (takeTCon (TCon tc0) = takeTCon (TForall t0))
        by (eapply makeTApps_takeTCon; eauto).
       snorm. nope.

     (* Can't happen, literals never have quantified types. *)
     * SSCase "x = XLit".
       destruct l0; snorm; congruence.

   (* The function part can take a step. *)
   + SCase "x steps".
     right.
     dest x'.
     exists (XAPP x' t2).
     lets D: EsContext XcAPP H1.
     eauto.


 (*************************************)
 (* Closed function abstractions are already values. *)
 - Case "XLam".
   left. 
   eapply type_wfX in H0. auto.


 (*************************************)
 - Case "XApp".
   right.
   inverts_type.
   edestruct IHx1; eauto.
   + SCase "value x1".
     edestruct IHx2; eauto.
     * SSCase "value x2".
       have (exists t x, x1 = XLam t x) as HF.
       destruct HF as [t11].
       destruct H2 as [x12].
       subst.
       exists (substXX 0 x2 x12). 
       apply EsLamApp; eauto.

     * SSCase "x2 steps".
       destruct H1 as [x2'].
       exists (XApp x1 x2'). auto.

   + SCase "x1 steps".
     destruct H0  as [x1'].
     exists (XApp x1' x2).
     eapply (EsContext (fun xx => XApp xx x2)); auto.


 (*************************************)
 - Case "XCon".
   inverts_type.

   (* All ctor args are either wnf or can step. *)
   assert (Forall (fun x => wnfX x \/ (exists x', STEP x x')) xs) as HWS.
   { repeat nforall. intros.
     have (exists t, TYPE ds nil nil x t). 
     destruct H2 as [t'].
     have (value x \/ (exists x', STEP x x')). 
     intuition.
   }

   (* All ctor args are wnf, or there is a context where one can step *)
   lets D: (@exps_ctx_run exp exp) HWS.
   inverts D.
   (* All ctor args are wnf *)
   + left.
     have (Forall (wfT 0) ts)
      by (rrwrite (0 = length (@nil ki));
          eapply kind_wfT_Forall2; eauto).

     have (Forall (wfX 0 0) xs)
      by (have (0 = length (@nil ki)) as HKL; 
          rewrite HKL at 1;
          rrwrite (0 = length (@nil ty)); eauto).
     eauto.

   + (* There is a context where one ctor arg can step *)
     right.
     dest C. dest x'. rip.
     lets D: step_context_XCon_exists H2 H4.
     destruct D as [x'']. eauto.


 (*************************************)
 - Case "XCase".
   right.
   inverts keep H1.
   have (value x \/ (exists x', STEP x x')) as HS.
   inverts HS. 

   (* Scrutinee is a value *)
   + SCase "x value".
     clear IHx.
     
     (* Consider the forms of the scrutinee. *)
     destruct x; nope.

     (* Can't happen, TForall is not a data type. *)
     * SSCase "XCase (XLAM x) alts".
       have (exists t', tObj = TForall t').
       dest t'. subst. nope.

     (* Can't happen, tFun is not a data type. *)
     * SSCase "XCase (XLam t x) alts".
       have (exists t11 t12, tObj = tFun t11 t12).
       dest t11. dest t12. subst.
       unfold tFun in H6. simpl in H6. inverts H6.
       have (DEFOK ds (DefDataType TyConFun ks dcs)) as HD.
       inverts HD. nope.

     (* When we have a well typed case match on some data object, 
        then there is a corresponding alternative. *)
     * SSCase "XCase (XCon d ts xs) alts".
       have (exists x, getAlt d aa = Some (AAlt d x)).
       dest x. exists (substXXs 0 l0 x).
       eapply EsCaseAlt; eauto.

     (* Can't happen, prim types are not data types. *)
     * SSCase "XCase (XLit l) alts".
       inverts_type.
       have HD: (DEFOK ds (DefDataType tcObj ks dcs)).
       inverts HD.
       destruct l; snorm; nope.

  (* Discriminant steps *)
  + SCase "x steps".
    destruct H2 as [x'].
    exists (XCase x' aa).
    lets D: EsContext XcCase; eauto.


 (*************************************)
 - Case "XPrim".
   inverts_type.
   right.

   (* All prim args are either wnf or can step. *)
   assert (Forall (fun x => wnfX x \/ (exists x', STEP x x')) xs) as HWS.
   { repeat nforall. intros.
     have (exists t, TYPE ds nil nil x t).
     destruct H2 as [t'].
     eapply H0 in H1.
     intuition. eauto.
   } 

   (* All ctor args are wnf, or there is a context where one can step. *)
   lets D: (@exps_ctx_run exp exp) HWS. inverts D.

   (* All arguments are wnf. *)
   + eapply progress_prim; eauto.

   (* One of the arguments can step. *)
   + dest C. dest x'. rip.
     lets D: step_context_XPrim_exists H2 H5.
     destruct D as [x'']. eauto.


 (*************************************)
 - Case "XLit".
   (* Literals are already values. *)
   inverts_type.
   left. eauto.


 (*************************************)
 - Case "XAlt".
   auto.
Qed.


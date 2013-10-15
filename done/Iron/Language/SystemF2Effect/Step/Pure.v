
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(********************************************************************)
(* Small Step Evaluation (pure rules)
   These are pure transitions that don't depend on the store. *)
Inductive StepP : exp  -> exp -> Prop :=

 (* Value application. *)
 | SpAppSubst
   :  forall t11 x12 v2
   ,  StepP (XApp (VLam t11 x12) v2)
            (substVX 0 v2 x12)

 (* Type application. *)
 | SpAPPSubst
   :  forall k11 x12 t2      
   ,  StepP (XAPP (VLAM k11 x12) t2)
            (substTX 0 t2 x12)

 (* Take the successor of a natural. *)
 | SpSucc
   :  forall n
   ,  StepP (XOp1 OSucc (VConst (CNat n)))
            (XVal (VConst (CNat (S n))))

 (* Test a natural for zero. *)
 | SpIsZero
   :  forall n
   ,  StepP (XOp1 OIsZero (VConst (CNat n)))
            (XVal (VConst (CBool (beq_nat n 0)))).

Hint Constructors StepP.


(********************************************************************)
(* Preservation for pure single step rules. *)
Lemma stepp_preservation
 :  forall se sp x x' t e
 ,  StepP  x x'
 -> Forall ClosedT se
 -> TypeX  nil nil se sp x  t e
 -> TypeX  nil nil se sp x' t e.
Proof.
 intros se sp x x' t e HS HC HT. gen t e.
 induction HS; intros; inverts_type; rip.

 Case "SpAppSubst".
  eapply subst_val_exp; eauto.

 Case "SpAPPSubst".
  rrwrite (TBot KEffect = substTT 0 t2 (TBot KEffect)).
  have HTE: (nil = substTE 0 t2 nil).
  have HSE: (se  = substTE 0 t2 se) by (symmetry; auto).
  rewrite HTE. rewrite HSE.
  eapply subst_type_exp; eauto.
   rrwrite (liftTE 0 se = se).
   snorm.

 Case "SpSucc".
  snorm. inverts H5. auto.

 Case "SpIsZero".
  snorm. inverts H5. auto.
Qed.


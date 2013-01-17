
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.
Require Import Iron.Language.SystemF2Effect.Theory.SubstTypeType.


Lemma typex_kind_type_effect
 :  forall ke te se sp v t e
 ,  TYPEX  ke te se sp v t e
 -> (KIND  ke sp t KData /\ KIND ke sp e KEffect).
Proof.
 intros. gen ke te se sp t e. 
 induction v using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  TYPEV  ke te se sp v t
      -> KIND   ke sp t KData);
   intros; inverts_type; eauto 1.

 Case "VLam".
  unfold tFun.
  lets D: IHv H8. rip.
   eapply KiApp.
    unfold appkind. burn.
    eapply KiApp.
    unfold appkind. burn.
    eapply KiApp.
    unfold appkind. burn.
    eapply KiCon0. simpl. eauto.
  auto. auto. auto.

 Case "VLAM".
  spec IHv H7. rip.

 Case "XConst".
  destruct c; simpl.
  unfold tUnit; burn.
  unfold tNat;  burn.
  unfold tBool; burn.

 Case "XVar".
  burn.

 Case "XApp".
  lets D1: IHv1 H10.
  lets D2: IHv2 H11.
  rip.

 Case "XLet".
  unfold tFun in *.
  lets D1: IHv H6.
  inverts D1.
  inverts H4.
  inverts H8.
  inverts H10.
  simpl in *.
  inverts H5. eauto.

 Case "XAPP".
  eapply IHv in H6.
  inverts_kind.
  rip.
  eapply subst_type_type; eauto.
 
 Case "XNew".
  spec IHv H7. rip.
  eapply lower_type_type_snoc; eauto.
  eapply lower_type_type_snoc; eauto.
  eapply maskOnVar_kind. eauto.

 Case "XUse".
  eapply IHv in H9.
  rip.
  eapply maskOnCap_kind. auto.

 Case "XAlloc". 
  unfold tRef. rip.
  eapply KiCon2. simpl. eauto.
  auto. eauto.
  unfold tAlloc in *.
  eapply KiCon1. norm. auto.
  
 Case "XRead".
  spec IHv H9.
  unfold tRef in *.
  inverts_kind; rip.
   destruct tc. norm. inverts H1. auto. 
   unfold tRead in *.
   destruct tc. norm. inverts H1.
   eapply KiCon1. simpl in *. eauto. eauto.

 Case "XWrite".
  unfold tUnit. rip. 
  unfold tWrite. 
  eapply KiCon1. norm. auto.

 Case "XOp1".
  destruct o; simpl in *; inverts H6; 
   unfold tNat; unfold tBool; rip.
Qed.
Hint Resolve typex_kind_type_effect.


Lemma typex_kind_type
 :  forall ke te se sp v t e
 ,  TYPEX  ke te se sp v t e
 -> KIND   ke sp t KData.
Proof. 
 intros. 
 lets D: typex_kind_type_effect H. rip.
Qed.
Hint Resolve typex_kind_type.


Lemma typex_kind_effect
 :  forall ke te se sp v t e
 ,  TYPEX  ke te se sp v t e
 -> KIND   ke sp e KEffect.
Proof. 
 intros. 
 lets D: typex_kind_type_effect H. rip.
Qed.
Hint Resolve typex_kind_effect.


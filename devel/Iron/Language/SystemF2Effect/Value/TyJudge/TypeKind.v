
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.
Require Import Iron.Language.SystemF2Effect.Theory.SubstTypeType.


Lemma typex_kind_type_effect
 :  forall ke te se sp v t e
 ,  TYPEX  ke te se sp v t e
 -> (KIND ke t KData /\ KIND ke e KEffect).
Proof.
 intros. gen ke te se sp t e. 
 induction v using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  TYPEV  ke te se sp v t
      -> KIND   ke t KData);
   intros; inverts_type; eauto 1.

 Case "VLam".
  unfold tFun.
  lets D: IHv H8. rip.
   eapply KIApp.
    unfold appkind. burn.
    eapply KIApp.
    unfold appkind. burn.
    eapply KIApp.
    unfold appkind. burn.
    eapply KICon. simpl. eauto.
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
  lets D1: IHv  H6.
  inverts D1.
  inverts H3.
  inverts H7.
  inverts H8.
  simpl in *.
  inverts H4. eauto.

 Case "XAPP".
  eapply IHv in H6.
  inverts_kind.
  rip.
  eapply subst_type_type; eauto.
 
 Case "XNew".
  eapply IHv in H7.
  rip.
  admit.                               (* go via lemma about lowerTT_substTT *)
  admit.

 Case "XUse".
  eapply IHv in H8.
  rip.

 Case "XAlloc". 
  unfold tRef. rip.
  eapply KIApp. unfold appkind. burn.
  eapply KIApp. unfold appkind. burn.
  eapply KICon. simpl. eauto.
  auto.
  spec IHv H9. auto.
  unfold tAlloc in *.
  eapply KIApp.
  unfold appkind; burn.
  eapply KICon; burn.
  auto.

 Case "XRead".
  spec IHv H9.
  unfold tRef in *.
  inverts IHv.
  unfold tFun in *.
  inverts H3.
  inverts H7.
  simpl in *.
  inverts H3.
  rip.
  unfold tRead.
  eapply KIApp.
  unfold appkind; burn.
  eapply KICon; burn.
  auto.

 Case "XWrite".
  unfold tUnit. rip. 
  unfold tWrite. 
  eapply KIApp.
   unfold appkind; burn.
   eapply KICon; burn. auto.

 Case "XSucc".
  unfold tNat. rip.

 Case "XIsZero".
  unfold tBool. rip.
Qed.
Hint Resolve typex_kind_type_effect.


Lemma typex_kind_type
 :  forall ke te se sp v t e
 ,  TYPEX  ke te se sp v t e
 -> KIND   ke t KData.
Proof. 
 intros. 
 lets D: typex_kind_type_effect H. rip.
Qed.
Hint Resolve typex_kind_type.


Lemma typex_kind_effect
 :  forall ke te se sp v t e
 ,  TYPEX  ke te se sp v t e
 -> KIND   ke e KEffect.
Proof. 
 intros. 
 lets D: typex_kind_type_effect H. rip.
Qed.
Hint Resolve typex_kind_effect.


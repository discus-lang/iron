
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.
Require Import Iron.Language.SystemF2Effect.Theory.SubstTypeType.


Lemma typex_kind_type
 :  forall ke te se sp v t e
 ,  TYPEX  ke te se sp v t e
 -> KIND   ke t KData.
Proof.
 intros. gen ke te se sp t e. 
 induction v using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  TYPEV  ke te se sp v t
      -> KIND   ke t KData);
   rip; inverts_type; eauto 3.

 Case "XLoc".
  admit.                                 (* need to know types in se are well kinded *)
  admit.

 Case "XLam".
  unfold tFun.
  lets D: IHv H8.
   eapply KIApp.
    unfold appkind. burn.
    eapply KIApp.
    unfold appkind. burn.
    eapply KIApp.
    unfold appkind. burn.
    eapply KICon. simpl. eauto.
  auto.
  admit.                                 (* need e2 effect *)
  auto.

 Case "XConst".
  destruct c; simpl.
  unfold tUnit; burn.
  unfold tNat;  burn.
  unfold tBool; burn.

 Case "XApp".
  eapply IHv in H6.
  eapply IHv0 in H9.
   unfold tFun in H6.
   inverts_kind.
   simpl in H4. inverts H4.
   auto.

 Case "XAPP".
  eapply IHv in H6.
  inverts_kind.
  eapply subst_type_type; eauto.
 
 Case "XNew".
  eapply IHv in H7.
  admit.                               (* go via lemma about lowerTT_substTT *)

 Case "XAlloc". 
  unfold tRef.
  eapply KIApp. unfold appkind. burn.
  eapply KIApp. unfold appkind. burn.
  eapply KICon. simpl. eauto.
  auto.
  spec IHv H9. auto.

 Case "XRead".
  spec IHv H9.
  unfold tRef in *.
  inverts IHv.
  unfold tFun in *.
  inverts H3.
  inverts H7.
  simpl in *.
  inverts H3.
  auto.

 Case "XWrite".
  unfold tUnit. auto.

 Case "XIsZero".
  unfold tBool. auto.
Qed.


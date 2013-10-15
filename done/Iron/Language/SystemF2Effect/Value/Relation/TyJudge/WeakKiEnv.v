
Require Import Iron.Language.SystemF2Effect.Type.
Require Import Iron.Language.SystemF2Effect.Value.Relation.TyJudge.


(* Weakening Kind Env in Type Judgement. *)
Lemma type_kienv_insert
 :  forall ke te se sp x1 t1 e1 k2 ix
 ,  TypeX  ke te se sp x1 t1 e1
 -> TypeX (insert ix k2 ke) (liftTE ix te)   (liftTE ix se)   sp
          (liftTX ix x1)    (liftTT 1 ix t1) (liftTT 1 ix e1).
Proof.
 intros. gen ix ke te se sp t1 e1 k2.
 induction x1 using exp_mutind with 
  (PV := fun v => forall ix ke te se sp k2 t3
               ,  TypeV ke te se sp v t3
               -> TypeV (insert ix k2 ke) (liftTE ix te)   (liftTE ix se) sp
                        (liftTV ix v)     (liftTT 1 ix t3));
   intros; inverts_type.

 - Case "VVar".
   simpl.
   apply TvVar; auto.
   apply get_map; auto.
   eauto using kind_kienv_insert.

 - Case "VLoc".
   simpl.
   eapply TvLoc; eauto;
    rrwrite ( TRef (liftTT 1 ix r) (liftTT 1 ix t)
            = liftTT 1 ix (TRef r t)).
   apply get_map; auto.
   eauto using kind_kienv_insert.

 - Case "VLam".
   simpl.
   apply TvLam.
    apply kind_kienv_insert. auto.
    rrwrite ( liftTE ix te :> liftTT 1 ix t
            = liftTE ix (te :> t)).
    spec IHx1 H8.
    burn.

 - Case "VLAM".
   simpl.
   eapply TvLAM. 
   rewrite insert_rewind. 
   rewrite (liftTE_liftTE 0 ix).
   rewrite (liftTE_liftTE 0 ix).
   rrwrite (TBot KEffect = liftTT 1 (S ix) (TBot KEffect)).
   eauto.

 - Case "XConst".
   simpl.
   eapply TvConst.
   destruct c; burn.
 
 - Case "XVal".
   simpl. auto.

 - Case "XLet".
   simpl.
   apply TxLet.
    auto using kind_kienv_insert.
    eauto.
    rrwrite ( liftTE ix te :> liftTT 1 ix t
            = liftTE ix (te :> t)).
    eauto.

 - Case "XApp".
   simpl.
   eapply TxApp.
    eapply IHx1 in H6. simpl in H6. eauto.
    eapply IHx0 in H9. eauto.

 - Case "XAPP".
   simpl.
   rewrite (liftTT_substTT' 0 ix). 
   simpl.
   eapply TvAPP.
   eapply (IHx1 ix) in H6. simpl in H6. eauto.
   auto using kind_kienv_insert.

 - Case "XOpPrim".
   simpl.
   destruct o; simpl in *.
    inverts H6.
     eapply TxOpPrim. simpl. eauto.
     rrwrite (TNat = liftTT 1 ix TNat). eauto.
    inverts H6.
     eapply TxOpPrim. simpl. eauto.
     rrwrite (TNat = liftTT 1 ix TNat). eauto.

 - Case "XPrivate".
   simpl.
   eapply TxPrivate
    with (t := liftTT 1 (S ix) t)
         (e := liftTT 1 (S ix) e).
 
   + eapply lowerTT_liftTT_succ. auto.

   + rrwrite (S ix = 1 + (0 + ix)).
     rewrite maskOnVarT_liftTT.
     eapply lowerTT_liftTT_succ. auto.

   + rewrite insert_rewind.
     rewrite (liftTE_liftTE 0 ix).
     rewrite (liftTE_liftTE 0 ix).
     eapply IHx1.
     have (liftTT 1 0 t1 = t).
     have (liftTT 1 0 e1 = maskOnVarT 0 e).
     repeat rewritess.
     auto.

 - Case "XExtend".
   simpl.
   rewrite (liftTT_substTT' 0 ix).
   eapply TxExtend
    with (e := liftTT 1 (S ix) e).
   + rrwrite (S ix = 1 + (0 + ix)).
     rewrite maskOnVarT_liftTT.
     eauto.

   + eauto using kind_kienv_insert.

   + simpl.
     rewrite insert_rewind.
     rewrite (liftTE_liftTE 0 ix).
     rewrite (liftTE_liftTE 0 ix).
     eapply IHx1. auto.

 - Case "XAlloc".
   eapply TxOpAlloc; eauto using kind_kienv_insert.

 - Case "XRead".
   eapply TxOpRead;  eauto using kind_kienv_insert.
   rrwrite ( TRef (liftTT 1 ix r) (liftTT 1 ix t1)
           = liftTT 1 ix (TRef r t1)).
   eauto.

 - Case "XWrite".
   eapply TxOpWrite; eauto using kind_kienv_insert.
   eapply IHx1 in H10. simpl in H10. eauto.
Qed.


Lemma type_kienv_weaken1
 :  forall ke te se sp x1 t1 e1 k2
 ,  TypeX  ke te se sp x1 t1 e1
 -> TypeX (ke :> k2)    (liftTE 0 te)   (liftTE 0 se)   sp
          (liftTX 0 x1) (liftTT 1 0 t1) (liftTT 1 0 e1).
Proof.
 intros.
 assert (ke :> k2 = insert 0 k2 ke) as HI.
  simpl. destruct ke; auto.
 rewrite HI.
 eapply type_kienv_insert; auto.
Qed.


Lemma typev_kienv_weaken1
 :  forall ke te se sp v1 t1 k2
 ,  TypeV  ke te se sp v1 t1
 -> TypeV (ke :> k2)    (liftTE 0 te) (liftTE 0 se) sp
          (liftTV 0 v1) (liftTT 1 0 t1).
Proof.
 intros.
 have HX: (TypeX ke te se sp (XVal v1) t1 (TBot KEffect)).
 eapply type_kienv_weaken1 in HX.
 simpl in HX.
 inverts HX. eauto.
Qed.


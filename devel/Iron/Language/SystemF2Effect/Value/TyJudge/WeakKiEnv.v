
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.


(* Weakening Kind Env in Type Judgement. *)
Lemma type_kienv_insert
 :  forall ix ke te se x1 t1 e1 k2
 ,  TYPEX ke te se x1 t1 e1
 -> TYPEX (insert ix k2 ke) (liftTE ix te)   (liftTE ix se) 
          (liftTX ix x1)    (liftTT 1 ix t1) (liftTT 1 ix e1).
Proof.
 intros. gen ix ke te se t1 e1 k2.
 induction x1 using exp_mutind with 
  (PV := fun v => forall ix ke te se k2 t3
               ,  TYPEV ke te se v t3
               -> TYPEV (insert ix k2 ke) (liftTE ix te)   (liftTE ix se)
                        (liftTV ix v)     (liftTT 1 ix t3));
   intros; inverts_type; simpl; eauto.

 Case "VVar".
  apply TvVar; auto.
  apply get_map; auto.

 Case "VLoc".
  eapply TvLoc; eauto.
  rrwrite ( tRef (liftTT 1 ix r) (liftTT 1 ix t)
          = liftTT 1 ix (tRef r t)).
  apply get_map; auto.

 Case "VLam".
  apply TvLam.
   apply kind_kienv_insert. auto.
   rrwrite ( liftTE ix te :> liftTT 1 ix t
           = liftTE ix (te :> t)).
   spec IHx1 H7.
   burn.

 Case "VLAM".
  eapply TvLAM. 
  rewrite insert_rewind. 
  rewrite (liftTE_liftTE 0 ix).
  rewrite (liftTE_liftTE 0 ix).
  rrwrite (TBot KEffect = liftTT 1 (S ix) (TBot KEffect)).
  eauto.

 Case "XLet".
  apply TxLet.
   auto using kind_kienv_insert.
   eauto.
   rrwrite ( liftTE ix te :> liftTT 1 ix t
           = liftTE ix (te :> t)).
   eauto.

 Case "XApp".
  eapply TxApp.
   eapply IHx1 in H5. simpl in H5. eauto.
   eapply IHx0 in H8. eauto.

 Case "XAPP".
  rewrite (liftTT_substTT' 0 ix). 
  simpl.
  eapply TvAPP.
  eapply (IHx1 ix) in H5. simpl in H5. eauto.
  auto using kind_kienv_insert.

 Case "XNew".
  eapply TxNew 
   with (t := liftTT 1 (S ix) t)
        (e := liftTT 1 (S ix) e).
  admit. admit.                    (* looks reasonable *)
  rewrite insert_rewind.
  rewrite (liftTE_liftTE 0 ix).
  rewrite (liftTE_liftTE 0 ix).
  auto.

 Case "XAlloc".
  eapply TxOpAlloc; eauto using kind_kienv_insert.

 Case "XRead".
  eapply TxOpRead;  eauto using kind_kienv_insert.
  rrwrite ( tRef (liftTT 1 ix r) (liftTT 1 ix t1)
          = liftTT 1 ix (tRef r t1)).
  eauto.

 Case "XWrite".
  eapply TxOpWrite; eauto using kind_kienv_insert.
  eapply IHx1 in H9. simpl in H9. eauto.
  eapply IHx1 in H7. eauto.

 Case "XIsZero".
  eapply TxOpIsZero.
  eapply IHx1 in H7. eauto.
Qed.


Lemma type_kienv_weaken1
 :  forall ke te se x1 t1 e1 k2
 ,  TYPEX ke te se x1 t1 e1
 -> TYPEX (ke :> k2)    (liftTE 0 te)   (liftTE 0 se) 
          (liftTX 0 x1) (liftTT 1 0 t1) (liftTT 1 0 e1).
Proof.
 intros.
 assert (ke :> k2 = insert 0 k2 ke) as HI.
  simpl. destruct ke; auto.
 rewrite HI.
 eapply type_kienv_insert; auto.
Qed.


Lemma typev_kienv_weaken1
 :  forall ke te se v1 t1 k2
 ,  TYPEV  ke te se v1 t1
 -> TYPEV (ke :> k2)    (liftTE 0 te) (liftTE 0 se)
          (liftTV 0 v1) (liftTT 1 0 t1).
Proof.
 intros.
 have HX: (TYPEX ke te se (XVal v1) t1 (TBot KEffect)).
 eapply type_kienv_weaken1 in HX.
 simpl in HX.
 inverts HX. eauto.
Qed.

Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.EquivT.
Require Export Iron.SystemF2Effect.Type.SubsT.
Require Export Iron.SystemF2Effect.Type.EquivTs.


Inductive SubsTs  : kienv -> stprops -> list ty -> list ty -> ki -> Prop :=
 | SbsSum 
   :  forall ke sp ts1 ts2 k
   ,  sumkind k
   -> Forall (fun t1 => KIND ke sp t1 k) ts1
   -> Forall (fun t2 => KIND ke sp t2 k) ts2
   -> Forall (fun t2 => In t2 ts1) ts2
   -> SubsTs ke sp ts1 ts2 k.


Lemma equivTs_subsTs
 :  forall ke sp t1 t2 k
 ,  sumkind k
 -> EquivTs ke sp t1 t2 k
 -> SubsTs  ke sp t1 t2 k.
Proof.
 intros.
 inverts H0.
 eapply SbsSum; auto.
Qed.


Lemma equivT_subsTs
 :  forall ke sp t1 t2 k
 ,  sumkind k
 -> EquivT ke sp t1 t2 k
 -> SubsTs ke sp (flattenT t1) (flattenT t2) k.
Proof.
 intros.
 eapply equivTs_subsTs; auto.
 eapply equivT_equivTs; auto.
Qed.


Lemma subsT_subsTs 
 :  forall ke sp t1 t2 k
 ,  sumkind k
 -> SubsT  ke sp t1             t2           k
 -> SubsTs ke sp (flattenT t1) (flattenT t2) k.
Proof.
 intros ke sp t1 t2 k HS HT.
 induction HT.
  Case "SbSumEquiv".
   eapply equivT_subsTs; auto.

  admit.                                   (* ok, need SubsTs trans *)
  admit.                                   (* ok, need SubsTs nil *)

  Case "SbSumAbove".
  { eapply SbsSum; rip.
    - have (KIND ke sp t1 k). 
      eapply flattenT_kind. 
      auto.
    - simpl. eapply Forall_app; eauto.
    - simpl. eapply Forall_app.
      inverts IHHT1. auto.
      inverts IHHT2. auto.
  }

 Case "SbSumBelow".
 { eapply SbsSum; rip.
   norm.
   simpl.
   inverts IHHT.
   norm.
 }
Qed.


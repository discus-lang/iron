
Require Export Iron.Language.SystemF2Effect.Type.Exp.Base.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindTs.
Require Export Iron.Language.SystemF2Effect.Type.Relation.EquivTs.


(********************************************************************)
Fixpoint flattenT (tt : ty) : list ty
 := match tt with
    | TSum t1 t2    => flattenT t1 ++ flattenT t2
    | TBot    _     => nil
    | _             => tt :: nil
    end.


(********************************************************************)
Lemma flattenT_kindTs
 :  forall ke sp t1 k
 ,  KindT  ke sp t1 k
 -> KindTs ke sp (flattenT t1) k.
Proof.
 intros. gen ke sp.
 induction t1; intros; simpl; eauto.

 Case "TSum". 
  inverts H.
  unfold KindTs in *.
   eapply Forall_app; eauto.
Qed.
Hint Resolve flattenT_kindTs.


Lemma equivT_equivTs 
 :  forall  ke sp t1 t2 k
 ,  SumKind k
 -> EquivT  ke sp t1 t2 k
 -> EquivTs ke sp (flattenT t1) (flattenT t2) k.
Proof.
 intros ke sp t1 t2 k HK HE.
 induction HE; intros.
  eapply equivTs_refl;  auto.
  eapply equivTs_sym;   auto.
  eapply equivTs_trans; auto.

 - Case "EqSumCong".
   simpl.
   spec IHHE1 HK.
   spec IHHE2 HK.
   eauto.

 - Case "EqSumBot".
   simpl. norm. 
   apply equivTs_refl; auto.
   
 - Case "EqSumIdemp".
   simpl.
   eapply EqsSum; norm; auto.
   + eapply in_app_split in H1.
     inverts H1; auto.

 - Case "EqSumComm".
   simpl.
   eapply EqsSum; snorm.

 - Case "EqSumAssoc".
   simpl.
   eapply EqsSum; auto.
   + norm. 
     eapply in_app_split in H3. inverts H3.
     eapply in_app_split in H4. inverts H4.
     auto. auto. auto.
   + norm.
     eapply in_app_split in H3. inverts H3. auto.
     eapply in_app_split in H4. inverts H4. 
     auto. auto.
Qed.

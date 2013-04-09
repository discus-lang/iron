
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.Relation.KindTs.
Require Export Iron.SystemF2Effect.Type.Relation.EquivTs.


Fixpoint flattenT (tt : ty) : list ty
 := match tt with
    | TVar    _     => tt :: nil
    | TForall _ _   => tt :: nil
    | TApp    _ _   => tt :: nil
    | TSum t1 t2    => flattenT t1 ++ flattenT t2
    | TBot    _     => nil
    | TCon0   _     => tt :: nil
    | TCon1   _ _   => tt :: nil
    | TCon2   _ _ _ => tt :: nil
    | TCap    _     => tt :: nil
    end.


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
 ,  sumkind k
 -> EquivT  ke sp t1 t2 k
 -> EquivTs ke sp (flattenT t1) (flattenT t2) k.
Proof.
 intros.
 induction H0.
  eapply equivTs_refl;  auto.
  eapply equivTs_sym;   auto.
  eapply equivTs_trans; auto.

 - Case "EqSumCong".
   simpl.
   spec IHEquivT1 H0.
   spec IHEquivT2 H0.
   eauto.

 - Case "EqSumBot".
   simpl. norm. 
   apply equivTs_refl; auto.
   
 - Case "EqSumIdemp".
   simpl.
   eapply EqsSum; norm; auto.
   + eapply in_app_split in H2.
     inverts H2; auto.

 - Case "EqSumComm".
   simpl.
   eapply EqsSum; snorm.

 - Case "EqSumAssoc".
   simpl.
   eapply EqsSum; auto.
   + norm. 
     eapply in_app_split in H4. inverts H4.
     eapply in_app_split in H5. inverts H5.
     auto. auto. auto.
   + norm.
     eapply in_app_split in H4. inverts H4. auto.
     eapply in_app_split in H5. inverts H5. 
     auto. auto.
Qed.

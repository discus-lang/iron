
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.Relation.EquivT.
Require Export Iron.SystemF2Effect.Type.Relation.SubsT.
Require Export Iron.SystemF2Effect.Type.Operator.FlattenT.


Inductive EquivTs : kienv -> stprops -> list ty -> list ty -> ki -> Prop :=
 | EqsSum
   :  forall ke sp ts1 ts2 k
   ,  sumkind k
   -> KindTs ke sp ts1 k
   -> KindTs ke sp ts2 k
   -> Forall (fun t2 => In t2 ts1) ts2
   -> Forall (fun t1 => In t1 ts2) ts1
   -> EquivTs ke sp ts1 ts2 k.

Hint Constructors EquivTs.


Lemma equivTs_refl
 :  forall  ke sp ts k
 ,  sumkind k
 -> KindTs  ke sp ts k
 -> EquivTs ke sp ts ts k.
Proof.
 intros.
 induction ts.
  eapply EqsSum; auto.
  eapply EqsSum; auto.
   norm. norm.
Qed.
Hint Resolve equivTs_refl.


Lemma equivTs_sym
 :  forall ke sp ts1 ts2 k
 ,  sumkind k
 -> KindTs  ke sp ts1 k
 -> KindTs  ke sp ts2 k
 -> EquivTs ke sp ts1 ts2 k
 -> EquivTs ke sp ts2 ts1 k.
Proof.
 intros. inverts H2.
 eapply EqsSum; auto.
Qed. 


Lemma equivTs_trans
 :  forall ke sp ts1 ts2 ts3 k
 ,  EquivTs ke sp ts1 ts2 k
 -> EquivTs ke sp ts2 ts3 k
 -> EquivTs ke sp ts1 ts3 k.
Proof.
 intros.
 inverts H. inverts H0.
 eapply EqsSum; snorm.
Qed.


Lemma equivTs_app
 :  forall ke sp ts1 ts1' ts2 ts2' k
 ,  EquivTs ke sp ts1 ts1' k
 -> EquivTs ke sp ts2 ts2' k
 -> EquivTs ke sp (ts1 ++ ts2) (ts1' ++ ts2') k.
Proof.
 intros.
 inverts H. inverts H0.
 eapply EqsSum; snorm.
  eapply in_app_split in H0. inverts H0.
   eauto. eauto.
  eapply in_app_split in H0. inverts H0.
   eauto. eauto.
Qed.
Hint Resolve equivTs_app.


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


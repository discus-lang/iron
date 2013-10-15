
Require Export Iron.Language.SystemF2Effect.Type.Exp.Base.
Require Export Iron.Language.SystemF2Effect.Type.Relation.EquivT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.SubsT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindTs.


(********************************************************************)
Inductive EquivTs : kienv -> stprops -> list ty -> list ty -> ki -> Prop :=
 | EqsSum
   :  forall ke sp ts1 ts2 k
   ,  SumKind k
   -> KindTs ke sp ts1 k
   -> KindTs ke sp ts2 k
   -> Forall (fun t2 => In t2 ts1) ts2
   -> Forall (fun t1 => In t1 ts2) ts1
   -> EquivTs ke sp ts1 ts2 k.


(********************************************************************)
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


Lemma equivTs_sumkind
 :  forall  ks sp ts1 ts2 k
 ,  EquivTs ks sp ts1 ts2 k
 -> SumKind k.
Proof. intros. inverts H; auto. Qed.
Hint Resolve equivTs_sumkind.


Lemma equivTs_kinds_left
 :  forall  ks sp ts1 ts2 k
 ,  EquivTs ks sp ts1 ts2 k
 -> KindTs  ks sp ts1 k.
Proof. intros. inverts H; auto. Qed.
Hint Resolve equivTs_kinds_left.


Lemma equivTs_kinds_right
 :  forall  ks sp ts1 ts2 k
 ,  EquivTs ks sp ts1 ts2 k
 -> KindTs  ks sp ts2 k.
Proof. intros. inverts H; auto. Qed.
Hint Resolve equivTs_kinds_right.


Lemma equivTs_refl
 :  forall  ke sp ts k
 ,  SumKind k
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
 ,  SumKind k
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



Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.Base.


(* Weaken store properties in kind judgement. *)
Lemma kind_stprops_snoc
 : forall ke sp p t k
 ,  KindT ke sp        t k
 -> KindT ke (p <: sp) t k.
Proof.
 intros. gen ke k.
 induction t; intros; inverts_kind; burn.

 Case "TCon2".
  destruct tc. norm. inverts H2. 
  eapply KiCon2.
  destruct t1. simpl in *. eauto.
  eauto. eauto.
Qed.
Hint Resolve kind_stprops_snoc.


Lemma kind_stprops_cons
 :  forall ke sp p t k
 ,  KindT ke sp t k
 -> KindT ke (sp :> p) t k.
Proof.
 intros. gen ke k.
 induction t; intros; inverts_kind; burn.
  
 Case "TCon2".
  destruct tc. snorm. inverts H2.
  eapply KiCon2; eauto.
  destruct t1. snorm.
Qed.
Hint Resolve kind_stprops_cons.

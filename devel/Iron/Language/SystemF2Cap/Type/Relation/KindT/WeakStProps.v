
Require Export Iron.Language.SystemF2Cap.Type.Relation.KindT.Base.


(* Weaken store properties in kind judgement. *)
Lemma kind_stprops_snoc
 : forall ke sp p t k
 ,  KindT ke sp        t k
 -> KindT ke (p <: sp) t k.
Proof.
 intros. gen ke k.
 induction t; intros; inverts_kind; burn.
Qed.
Hint Resolve kind_stprops_snoc.


Lemma kind_stprops_cons
 :  forall ke sp p t k
 ,  KindT ke sp t k
 -> KindT ke (sp :> p) t k.
Proof.
 intros. gen ke k.
 induction t; intros; inverts_kind; burn.
Qed.
Hint Resolve kind_stprops_cons.

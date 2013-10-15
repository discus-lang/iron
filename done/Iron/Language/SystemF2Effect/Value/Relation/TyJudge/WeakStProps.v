
Require Import Iron.Language.SystemF2Effect.Value.Relation.TyJudge.


(* Weakening Store Properties in Type Judgement *)
Lemma typex_stprops_snoc
 :  forall ke te se sp x t e p
 ,  TypeX  ke te se sp        x t e
 -> TypeX  ke te se (p <: sp) x t e.
Proof.
 intros. gen ke te se sp t e p.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t p
      ,  TypeV ke te se sp v t
      -> TypeV ke te se (p <: sp) v t);
  intros; inverts_type; 
  eauto using kind_stprops_snoc.
Qed.
Hint Resolve typex_stprops_snoc.


Lemma typev_stprops_snoc
 :  forall ke te se sp        v t p
 ,  TypeV  ke te se sp        v t
 -> TypeV  ke te se (p <: sp) v t. 
Proof.
 intros.
 have HX: (TypeX ke te se (p <: sp) (XVal v) t (TBot KEffect)).
 inverts HX.
 trivial.
Qed.
Hint Resolve typev_stprops_snoc.


Lemma typex_stprops_cons
 :  forall ke te se sp x t e p
 ,  TypeX  ke te se sp        x t e
 -> TypeX  ke te se (sp :> p) x t e.
Proof.
 intros. gen ke te se sp t e p.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t p
      ,  TypeV ke te se sp v t
      -> TypeV ke te se (sp :> p) v t);
  intros; inverts_type; 
  eauto using kind_stprops_cons.
Qed.
Hint Resolve typex_stprops_cons.


Lemma typev_stprops_cons
 :  forall ke te se sp v t p
 ,  TypeV  ke te se sp v t
 -> TypeV  ke te se (sp :> p) v t.
Proof.
 intros.
 have HX: (TypeX ke te se (sp :> p) (XVal v) t (TBot KEffect)).
 inverts HX.
 trivial.
Qed.
Hint Resolve typev_stprops_cons.


Lemma typex_stprops_weaken
 :  forall ke te se sp1 sp2 x t e
 ,  TypeX  ke te se sp1          x t e
 -> TypeX  ke te se (sp2 >< sp1) x t e.
Proof.
 intros. gen ke te se sp1 t e.
 induction sp2; intros; burn.
 rrwrite ((sp2 :> a) >< sp1 = sp2 >< (a <: sp1)).
 burn.
Qed.
Hint Resolve typex_stprops_weaken.


Lemma typex_stprops_extends
 :  forall ke te se sp1 sp2 x t e
 ,  extends sp2 sp1
 -> TypeX  ke te se sp1 x t e
 -> TypeX  ke te se sp2 x t e.
Proof.
 intros.
 unfold extends in *.
 destruct H as [sp3]. subst.
 burn using typex_stprops_weaken.
Qed.
Hint Resolve typex_stprops_extends.


Lemma typev_stprops_extends
 :  forall ke te se sp1 sp2 v t
 ,  extends sp2 sp1 
 -> TypeV ke te se sp1 v t
 -> TypeV ke te se sp2 v t.
Proof.
 intros.
 unfold extends in *.
 destruct H as [sp3]. subst.
 have HX: (TypeX ke te se (sp3 >< sp1) (XVal v) t (TBot KEffect)).
 inverts HX.
 eauto.
Qed.
Hint Resolve typev_stprops_extends.


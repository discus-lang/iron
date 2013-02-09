
Require Export Iron.SystemF2Effect.Type.KiJudge.Base.


(* Weaken store properties in kind judgement. *)
Lemma kind_stprops_snoc
 : forall ke sp p t k
 ,  KIND ke sp        t k
 -> KIND ke (p <: sp) t k.
Proof.
 intros. gen ke k.
 induction t; intros; inverts_kind; burn.

 Case "TCon2".
  destruct tc. norm. inverts H2. 
  eapply KiCon2.
  destruct t1. simpl in *. eauto.
  eauto. eauto.
Qed.


Lemma kind_stprops_cons
 :  forall ke sp p t k
 ,  KIND ke sp t k
 -> KIND ke (sp :> p) t k.
Proof.
 intros. gen ke k.
 induction t; intros; inverts_kind; burn.
  
 Case "TCon2".
  destruct tc. snorm. inverts H2.
  eapply KiCon2; eauto.
  destruct t1. snorm.
Qed.

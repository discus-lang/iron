
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.


(* Weakening Store Typing in Type Judgement. *)
Lemma typex_stenv_snoc 
 :  forall ke te se sp t2 x t1 e1
 ,  closedT t2
 -> TYPEX  ke te se         sp x t1 e1
 -> TYPEX  ke te (t2 <: se) sp x t1 e1.
Proof.
 intros. gen ke te se sp t1 e1 t2.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se sp t1 t2
      ,  closedT t2
      -> TYPEV ke te se         sp v t1
      -> TYPEV ke te (t2 <: se) sp v t1)
  ; intros; inverts_type; eauto.

 Case "VLAM".
  eapply TvLAM.
  spec IHx H8 H. clear H8.
  unfold liftTE in *.
  simpl. norm. 
  rrwrite (liftTT 1 0 t2 = t2).
  auto.

 Case "XNew".
  eapply TxNew with (t := t) (e := e); eauto.
  spec IHx H8 H. clear H8.
  unfold liftTE in *.
  simpl. norm.
  rrwrite (liftTT 1 0 t2 = t2).
  auto.
Qed.
Hint Resolve typex_stenv_snoc.


Lemma typev_stenv_snoc
 :  forall ke te se sp t2 v t1
 ,  closedT t2
 -> TYPEV ke te se         sp v t1
 -> TYPEV ke te (t2 <: se) sp v t1.
Proof.
 intros.
 have HX: (TYPEX ke te se sp (XVal v) t1 (TBot KEffect)).
 eapply typex_stenv_snoc in HX.
 inverts HX; eauto.
 eauto.
Qed.
Hint Resolve typev_stenv_snoc.


Lemma typex_stenv_weaken
 :  forall ke te se1 se2 sp x t1 e1
 ,  Forall closedT se2
 -> TYPEX  ke te  se1         sp x t1 e1
 -> TYPEX  ke te (se2 >< se1) sp x t1 e1.
Proof.
 intros. gen ke te se1 sp.
 induction se2; intros.
  burn.
  rrwrite ((se2 :> a) >< se1 = se2 >< (a <: se1)).
  inverts H. rip.
Qed.
Hint Resolve typex_stenv_weaken.


Lemma typex_stenv_extends
 :  forall ke te se1 se2 sp x t1 e1
 ,  Forall closedT se2
 -> extends se2 se1
 -> TYPEX ke te se1 sp x t1 e1
 -> TYPEX ke te se2 sp x t1 e1.
Proof.
 intros.
 unfold extends in *.
 destruct H0 as [se3]. subst.
 eapply typex_stenv_weaken; auto.
  eauto.
Qed.
Hint Resolve typex_stenv_extends.


Lemma typev_stenv_extends
 :  forall ke te sp se1 se2 v t1
 ,  Forall closedT se2
 -> extends se2 se1
 -> TYPEV ke te se1 sp v t1
 -> TYPEV ke te se2 sp v t1.
Proof.
 intros.
 unfold extends in *.
 destruct H0 as [se3]. subst.
 assert (TYPEX ke te (se3 >< se1) sp (XVal v) t1 (TBot KEffect)) as HX.
  eauto.
 inverts HX. auto.
Qed.
Hint Resolve typex_stenv_extends.


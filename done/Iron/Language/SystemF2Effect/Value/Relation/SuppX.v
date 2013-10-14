
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Value.Relation.TyJudge.


Fixpoint suppV (l : nat) (vv : val) : Prop := 
 match vv with
 | VVar n'            => False
 | VLoc l'            => l = l'
 | VLam t x           => suppX l x
 | VLAM k x           => suppX l x
 | VConst _           => False
 end
 with   suppX (l : nat) (xx : exp) : Prop :=
 match xx with
 | XVal     v         => suppV l v
 | XLet     t x1 x2   => suppX l x1 \/ suppX l x2
 | XApp     v1 v2     => suppV l v1 \/ suppV l v2
 | XAPP     v1  t2    => suppV l v1
 | XOp1     op v      => suppV l v
 | XPrivate x         => suppX l x
 | XExtend  t x       => suppX l x
 | XAlloc   t v1      => suppV l v1
 | XRead    t v1      => suppV l v1
 | XWrite   t v1 v2   => suppV l v1 \/ suppV l v2
 end.


Definition coversX (se : stenv) (x : exp)
 := forall l, suppX l x -> (exists t, get l se = Some t).
Hint Unfold coversX.

Definition coversV (se : stenv) (v : val)
 := forall l, suppV l v -> (exists t, get l se = Some t).
Hint Unfold coversV.


Lemma typeX_coversX
 :  forall ke te se sp x t e
 ,  TYPEX  ke te se sp x t e
 -> coversX se x.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  TYPEV ke te se sp v t
      -> coversV se v); intros;
  try (solve [inverts_type; 
             unfold coversV in *; snorm;
             unfold coversX in *; snorm; eauto]).

 - inverts_type.
   unfold coversV. intros.
   inverts_kind. snorm. subst.
   eauto.

 - inverts_type.  
   unfold coversV in *. snorm.
   unfold coversX in *. snorm.
   eapply IHx in H7; eauto.
   destruct H7.
   unfold liftTE in *.   
   eapply get_map_exists in H0. 
   firstorder.

 - inverts_type.
   unfold coversX in *. simpl.
   intros. inverts H.
   + eapply IHx1; eauto.
   + eapply IHx2; eauto.

 - inverts_type.
   unfold coversX in *. simpl.
   intros. inverts H.
   + eapply IHx; eauto.
   + eapply IHx0; eauto.

 - inverts_type.
   unfold coversX in *. snorm.
   eapply IHx in H7; eauto.
   destruct H7.
   unfold liftTE in *.
   eapply get_map_exists in H0. 
   firstorder.
   
 - inverts_type.
   unfold coversX in *. snorm.
   eapply IHx in H10; eauto.
   destruct H10.
   unfold liftTE in *.
   eapply get_map_exists in H0. 
   firstorder.

 - inverts_type.
   unfold coversX in *. simpl.
   intros. inverts H.
   + eapply IHx; eauto.
   + eapply IHx0; eauto.
Qed.


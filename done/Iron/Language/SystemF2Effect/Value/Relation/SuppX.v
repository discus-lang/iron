
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Value.Relation.TyJudge.


Fixpoint SuppV (l : nat) (vv : val) : Prop := 
 match vv with
 | VVar n'            => False
 | VLoc l'            => l = l'
 | VLam t x           => SuppX l x
 | VLAM k x           => SuppX l x
 | VConst _           => False
 end
 with   SuppX (l : nat) (xx : exp) : Prop :=
 match xx with
 | XVal     v         => SuppV l v
 | XLet     t x1 x2   => SuppX l x1 \/ SuppX l x2
 | XApp     v1 v2     => SuppV l v1 \/ SuppV l v2
 | XAPP     v1  t2    => SuppV l v1
 | XOp1     op v      => SuppV l v
 | XPrivate x         => SuppX l x
 | XExtend  t x       => SuppX l x
 | XAlloc   t v1      => SuppV l v1
 | XRead    t v1      => SuppV l v1
 | XWrite   t v1 v2   => SuppV l v1 \/ SuppV l v2
 end.


Definition CoversX (se : stenv) (x : exp)
 := forall l, SuppX l x -> (exists t, get l se = Some t).
Hint Unfold CoversX.

Definition CoversV (se : stenv) (v : val)
 := forall l, SuppV l v -> (exists t, get l se = Some t).
Hint Unfold CoversV.


Lemma typeX_coversX
 :  forall ke te se sp x t e
 ,  TypeX  ke te se sp x t e
 -> CoversX se x.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  TypeV ke te se sp v t
      -> CoversV se v); intros;
  try (solve [inverts_type; 
             unfold CoversV in *; snorm;
             unfold CoversX in *; snorm; eauto]).

 - inverts_type.
   unfold CoversV. intros.
   inverts_kind. snorm. subst.
   eauto.

 - inverts_type.  
   unfold CoversV in *. snorm.
   unfold CoversX in *. snorm.
   eapply IHx in H7; eauto.
   destruct H7.
   unfold liftTE in *.   
   eapply get_map_exists in H0. 
   firstorder.

 - inverts_type.
   unfold CoversX in *. simpl.
   intros. inverts H.
   + eapply IHx1; eauto.
   + eapply IHx2; eauto.

 - inverts_type.
   unfold CoversX in *. simpl.
   intros. inverts H.
   + eapply IHx; eauto.
   + eapply IHx0; eauto.

 - inverts_type.
   unfold CoversX in *. snorm.
   eapply IHx in H7; eauto.
   destruct H7.
   unfold liftTE in *.
   eapply get_map_exists in H0. 
   firstorder.
   
 - inverts_type.
   unfold CoversX in *. snorm.
   eapply IHx in H10; eauto.
   destruct H10.
   unfold liftTE in *.
   eapply get_map_exists in H0. 
   firstorder.

 - inverts_type.
   unfold CoversX in *. simpl.
   intros. inverts H.
   + eapply IHx; eauto.
   + eapply IHx0; eauto.
Qed.


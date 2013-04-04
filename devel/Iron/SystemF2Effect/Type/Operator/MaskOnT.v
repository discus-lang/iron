
Require Import Iron.SystemF2Effect.Type.Relation.KindT.
Require Import Iron.SystemF2Effect.Type.Relation.SubsT.
Require Import Iron.SystemF2Effect.Type.Relation.SubsTs.
Require Import Iron.SystemF2Effect.Type.Operator.FreeTT.
Require Import Iron.SystemF2Effect.Type.Operator.LiftTT.
Require Import Iron.SystemF2Effect.Type.Operator.SubstTT.
Require Import Iron.SystemF2Effect.Type.Exp.
Require Import Coq.Bool.Bool.


(* Mask effects on the given region, 
   replacing with the bottom effect. *)
Fixpoint maskOnT (p : ty -> bool) (e : ty) : ty
 := match e with
    |  TVar tc        => e
    |  TForall k t1   => e
    |  TApp t1 t2     => e
    |  TSum t1 t2     => TSum (maskOnT p t1) (maskOnT p t2)
    |  TBot k         => e

    |  TCon0 tc       => e

    |  TCon1 tc t1
    => if p e     then TBot KEffect
                  else e

    |  TCon2 tc t1 t2 => e
    
    |  TCap  tc       => e
    end.
Arguments maskOnT p e : simpl nomatch.


Definition maskOnVarT    (n : nat) (e : ty) : ty
 := maskOnT (isEffectOnVar n) e.

Definition maskOnCapT    (n : nat) (e : ty) : ty
 := maskOnT (isEffectOnCap n) e.


(********************************************************************)
Lemma isEffectOnVar_freeTT_false
 :  forall d t
 ,  freeTT d t = false
 -> isEffectOnVar d t = false.
Proof.
 intros. 
 destruct t; snorm.
  destruct t0; snorm; 
   try rewrite andb_false_iff; rip.
  right.
  rewrite beq_nat_false_iff. auto.
Qed.
Hint Resolve isEffectOnVar_freeTT_false.


(********************************************************************)
Lemma maskOnT_kind
 :  forall ke sp t k p
 ,  KindT  ke sp t k 
 -> KindT  ke sp (maskOnT p t) k.
Proof.
 intros. gen ke sp k.
 induction t; intros; inverts_kind; simpl; eauto.

 - Case "TCon1".
   unfold maskOnT. 
   split_if.
   + destruct t; snorm.
      inverts H4. auto.
      inverts H4. auto.
      inverts H4. auto.
   + destruct t; snorm;
      inverts H4; eapply KiCon1; simpl; eauto.

 - Case "TCon2".
   destruct tc.
   snorm. inverts H2.
   spec IHt1 H5.
   spec IHt2 H7.
   eapply KiCon2. 
    destruct t1. snorm.
    eauto. eauto.
Qed.
Hint Resolve maskOnT_kind.


Lemma maskOnVarT_kind
 :  forall ke sp t k n
 ,  KindT  ke sp t k
 -> KindT  ke sp (maskOnVarT n t) k.
Proof.
 intros. 
 unfold maskOnVarT. 
 eapply maskOnT_kind; auto.
Qed.
Hint Resolve maskOnVarT_kind.


Lemma maskOnCapT_kind
 :  forall ke sp t k n
 ,  KindT  ke sp t k
 -> KindT  ke sp (maskOnCapT n t) k.
Proof.
 intros.
 unfold maskOnVarT.
 eapply maskOnT_kind; auto.
Qed.
Hint Resolve maskOnCapT_kind.


(********************************************************************)
Lemma maskOnVarT_freeTT_id
 :  forall d t 
 ,  freeTT d t = false 
 -> maskOnVarT d t = t.
Proof.
 intros. gen d.
 induction t; intros; 
  try (solve [unfold maskOnVarT; snorm]).

 - Case "TSum".
   unfold maskOnVarT in *.
   snorm.
   apply orb_false_iff in H. rip.
   repeat rewritess; auto.

 - Case "TCon1".
   unfold maskOnVarT in *.
   snorm.
   unfold maskOnT.
   split_if.
   + destruct t0; 
      try (solve [snorm;
                  symmetry in HeqH0; 
                  rewrite andb_true_iff in HeqH0; rip; nope]).
      * SCase "TVar".
        simpl in H.
        snorm.
        symmetry in HeqH0.        
        rewrite andb_true_iff in HeqH0. rip.
        snorm. subst. nope.
   +  auto. 
Qed.


(********************************************************************)
Lemma maskOnVarT_liftTT
 :  forall r d e
 ,  maskOnVarT r (liftTT 1 (1 + (r + d)) e) 
 =  liftTT 1 (1 + (r + d)) (maskOnVarT r e).
Proof.
 intros. gen r d.
 induction e; intros; 
  try (solve [simpl; burn]);
  try (solve [simpl; f_equal; rewritess; auto]).

 - Case "TSum".
   simpl.
   unfold maskOnVarT in *.
   simpl. f_equal. eauto. eauto.

 - Case "TCon1".
   unfold maskOnVarT in *.
   simpl.
   unfold maskOnT. 
   split_if. 
   + split_if.
     * simpl. auto.
     * snorm.
       apply beq_true_split  in HeqH. rip.
       apply beq_false_split in HeqH0.
       inverts HeqH0.
        congruence.
        eapply liftTT_isTVar_true in H0. 
         congruence. omega.
   + split_if.
     * snorm.
       apply beq_true_split  in HeqH0. rip.
       apply beq_false_split in HeqH.
       inverts HeqH.
        congruence.
        apply isTVar_form in H0. subst.
        rewrite liftTT_TVar_above in H1.
        simpl in H1. 
        rewrite <- beq_nat_refl in H1. 
         nope. omega.
     * simpl. auto.
Qed.
Hint Resolve maskOnVarT_liftTT.


(********************************************************************)
Lemma maskOnVarT_substTT
 :  forall d d' t1 t2
 ,  freeTT d t2 = false
 -> maskOnVarT d (substTT (1 + d' + d) t2 t1)
 =  substTT (1 + d' + d) (maskOnVarT d t2) (maskOnVarT d t1).
Proof.
 intros. gen d t2.
 induction t1; intros; 
   try (solve [simpl; burn]).

 - Case "TForall".
   unfold maskOnVarT in *.
   snorm.
   f_equal. f_equal.
   lets D: maskOnVarT_freeTT_id. unfold maskOnVarT in *.
   rewritess; auto.
 
 - Case "TApp".
   unfold maskOnVarT in *.
   snorm.
   f_equal. 
   + f_equal. 
     lets D: maskOnVarT_freeTT_id. unfold maskOnVarT in *.
     rewritess; auto.
   + f_equal.
     lets D: maskOnVarT_freeTT_id. unfold maskOnVarT in *.
     rewritess; auto.

 - Case "TSum".
   unfold maskOnVarT in *.
   snorm.
   f_equal.
   + rewritess; auto.
   + rewritess; auto.

 - Case "TCon1".
   unfold maskOnVarT.
   unfold maskOnT; split_if; fold maskOnT.
   + simpl.
     snorm. 
     apply beq_true_split in HeqH0. rip.
     apply isTVar_form in H1. subst.
     spec IHt1 d t2. rip.
     snorm.
     * omega.
     * unfold maskOnT.
       split_if; auto.
       eapply beq_false_split in HeqH0. 
       inverts HeqH0.
        congruence.
        snorm. nope.
     * unfold maskOnT.
       split_if; auto.
       unfold isEffectOnVar in HeqH0.
       eapply beq_false_split in HeqH0.
       inverts HeqH0.
        congruence.
        snorm. omega.

   + simpl. 
     unfold maskOnT; split_if; fold maskOnT.

     * unfold isEffectOnVar in HeqH0.
       unfold isEffectOnVar in HeqH1.
       apply beq_false_split in HeqH0.
       apply beq_true_split in HeqH1. 
       rip. 
       inverts HeqH0. 
        congruence.
        apply isTVar_form in H1.
        destruct t1; snorm; try congruence.
         subst. snorm. nope.
         inverts H1. omega.

     * repeat f_equal.
       lets D: maskOnVarT_freeTT_id. unfold maskOnVarT in *.
       erewrite D; auto.
  
 - Case "TCon2".
   unfold maskOnVarT in *.
   snorm. 
   f_equal.
   + f_equal.
     lets D: maskOnVarT_freeTT_id. unfold maskOnVarT in *.
     rewritess; auto.
   + f_equal.
     lets D: maskOnVarT_freeTT_id. unfold maskOnVarT in *.
     rewritess; auto.
Qed.

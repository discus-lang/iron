
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Lift.
Require Import Iron.Language.SystemF2Effect.Type.Subst.
Require Import Iron.Language.SystemF2Effect.Type.KiJudge.


(* Mask effects on the given region, 
   replacing with the bottom effect. *)
Fixpoint maskOnVar (r : nat) (e : ty) : ty
 := match e with
    |  TVar tc       => TVar tc
    |  TForall k t1  => TForall k (maskOnVar (S r) t1)
    |  TApp t1 t2    => TApp (maskOnVar r t1) (maskOnVar r t2)
    |  TSum t1 t2    => TSum (maskOnVar r t1) (maskOnVar r t2)
    |  TBot k        => TBot k

    |  TCon0 tc      => TCon0 tc

    |  TCon1 tc t1
    => match t1 with
       | TVar n' 
       => if beq_nat r n' 
             then TBot KEffect 
             else TCon1 tc (maskOnVar r t1)

       | _ =>     TCon1 tc (maskOnVar r t1)
       end
    
    | TCon2 tc t1 t2 => TCon2 tc (maskOnVar r t1) (maskOnVar r t2)

    | TCap  tc       => TCap tc
    end.
Arguments maskOnVar r e : simpl nomatch.


(********************************************************************)
(* Helper lemmas *)
Lemma maskOnVar_TBot_cases
 :  forall d tc n
 ,  maskOnVar d (TCon1 tc (TVar n)) = TBot KEffect 
 -> d = n.
Proof.
 intros.
 unfold maskOnVar in H.
 break (beq_nat d n).
  norm_beq_nat. auto.
  nope.
Qed.


Lemma maskOnVar_TCon1_cases
 :   forall d tc t
 ,   maskOnVar d (TCon1 tc t) = TBot KEffect
 \/  maskOnVar d (TCon1 tc t) = TCon1 tc (maskOnVar d t).
Proof.
 intros. 
 destruct t; simpl; rip.
 unfold maskOnVar. snorm.
Qed.


Lemma maskOnVar_match
 : forall n t
 , maskOnVar n (TCon1 t (TVar n)) = TBot KEffect.
Proof.
 intros.
 unfold maskOnVar.
 snorm. omega.
Qed.
Hint Resolve maskOnVar_match.
Hint Rewrite maskOnVar_match : global.


Lemma maskOnVar_nomatch
 : forall d tc t2
 ,  t2 <> TVar d
 -> maskOnVar d (TCon1 tc t2)    = TCon1 tc (maskOnVar d t2).
Proof.
 intros.
 destruct t2; snorm.
 
 Case "TVar".
  unfold maskOnVar. 
  snorm. congruence.
Qed.


(********************************************************************)
Lemma maskOnVar_kind
 :  forall ke sp t k n
 ,  KIND ke sp t k 
 -> KIND ke sp (maskOnVar n t) k.
Proof.
 intros. gen ke sp n k.
 induction t; intros; inverts_kind; simpl; auto.
  
 Case "TApp".
  spec IHt1 H5.
  spec IHt2 H7.
  eapply KiApp; eauto.

 Case "TCon1".
  spec IHt H6.
  destruct t0; simpl in *; eauto.
  destruct t;  snorm; inverts H4;
  unfold maskOnVar; split_if; snorm; eauto;
   eapply KiCon1; snorm; eauto. 

 Case "TCon2".
  spec IHt1 H5.
  spec IHt2 H7.
  eapply KiCon2; eauto.
   destruct tc; destruct t1; norm.
Qed.


(********************************************************************)
Lemma liftTT_maskOnVar
 :  forall r d t
 ,  maskOnVar r (liftTT 1 (1 + (r + d)) t) 
 =  liftTT 1 (1 + (r + d)) (maskOnVar r t).
Proof.
Opaque le_gt_dec.

 intros. gen r d.
 induction t; intros; 
   try (solve [simpl; burn]);
   try (solve [simpl; f_equal; rewritess; auto]).

 Case "TForall".
  simpl. f_equal.
  rrwrite (S (S (r + d)) = 1 + ((S r) + d)).
  rewrite IHt. auto.

 Case "TCon1".
  simpl.
  destruct t0.

  SCase "TVar".
   repeat (unfold maskOnVar; simpl; 
           try split_dec; try split_if; try norm_beq_nat; 
           try omega; auto).
          
  (* GAH. Most of this rubbish is just to force single step evaluation of mask.
     I can't work out how to do a 'simpl' with only a single step *)
  SCase "TForall".
   simpl liftTT.
   set     (X0 := TForall k (liftTT 1 (S (S (r + d))) t0)).
   rrwrite (maskOnVar r (TCon1 t X0)        = TCon1 t (maskOnVar r X0)).
   subst X0.
   rrwrite (TForall k (liftTT 1 (S (S (r + d))) t0) = liftTT 1 (S (r + d)) (TForall k t0)).
   rewritess. simpl. auto.
  
  SCase "TApp".
   simpl liftTT.
   set      (X0 := TApp (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)).
    rrwrite (maskOnVar r (TCon1 t X0)       = TCon1 t (maskOnVar r X0)).
   subst X0.
   rrwrite  ( TApp (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)
            = liftTT 1 (S (r + d)) (TApp t0_1 t0_2)).
   rewritess. simpl. auto.

  SCase "TSum".
   simpl liftTT.
   set      (X0 := TSum (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)).
    rrwrite (maskOnVar r (TCon1 t X0)      = TCon1 t (maskOnVar r X0)).
   subst X0.
   rrwrite  ( TSum (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)
            = liftTT 1 (S (r + d)) (TSum t0_1 t0_2)).
   rewritess. simpl. auto.

 SCase "TBot".
  burn.

 SCase "TCon0".
  burn.

 SCase "TCon1".
  simpl liftTT.
  set    (X0 := TCon1 t0 (liftTT 1 (S (r + d)) t1)).
   rrwrite (maskOnVar r (TCon1 t X0)       = TCon1 t (maskOnVar r X0)).
  subst X0.
  rrwrite  ( TCon1 t0 (liftTT 1 (S (r + d)) t1)
           = liftTT 1 (S (r + d)) (TCon1 t0 t1)).
  rewritess. auto.

  SCase "TCon2".
   simpl liftTT.
   set      (X0 := TCon2 t0 (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)).
    rrwrite (maskOnVar r (TCon1 t X0)      = TCon1 t (maskOnVar r X0)).
   subst X0.
   rrwrite  ( TCon2 t0 (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)
            = liftTT 1 (S (r + d)) (TCon2 t0 t0_1 t0_2)).
   rewritess. simpl. auto.

 SCase "TCap".
  burn.
Qed.


(********************************************************************)
Lemma mask_liftTT
  : forall d d' t
  , maskOnVar (1 + d' + d) (liftTT 1 d t) 
  = liftTT 1 d (maskOnVar (d' + d) t).
Proof. 
Opaque beq_nat.
 intros. gen d d'.
 induction t; intros;
  try (solve [simpl; f_equal; burn]).

  Case "TForall".  
   simpl. f_equal.
    rrwrite (S (S (d' + d)) = 1 + d' + (S d)).  
    rewrite IHt. 
    rrwrite (d' + S d = S (d' + d)).
    auto.

  Case "TCon1".
   simpl.
   destruct t0; 
    try (solve [simpl in *; f_equal; rip; rewritess; f_equal]).

   SCase "TVar". 
    lets D: maskOnVar_TCon1_cases (d' + d) t (TVar n).
    inverts D.

    SSCase "Effect masked".
     assert (d' + d = n).
      eapply maskOnVar_TBot_cases; eauto.
     repeat rewritess.
     snorm. omega.

    SSCase "Effect not masked".
     rewritess.
     set (X := maskOnVar (d' + d) (TVar n)).
     rrwrite (liftTT 1 d (TCon1 t X) = TCon1 t (liftTT 1 d X)).
     subst X.
     rewrite <- IHt. clear IHt.

     snorm; 
      unfold maskOnVar in *; snorm;
      try rewritess; try nope; omega.
Qed.


Lemma mask_substTT
  : forall d d' t1 t2
  ,  t2 <> TVar d
  -> maskOnVar d (substTT (1 + d' + d) t2 t1)
  =  substTT (1 + d' + d) (maskOnVar d t2) (maskOnVar d t1).
Proof.
 intros. gen d d' t2.
 induction t1; intros;
  try (solve [repeat (snorm; f_equal)]).

  Case "TForall".
   simpl. f_equal.
   rrwrite (S (S (d' + d)) = 1 + d' + (S d)).
   rewrite IHt1. f_equal.
   rrwrite (S d = 1 + d + 0).
   rewrite mask_liftTT.
   burn. burn.

  Case "TCon1".
   simpl.
   destruct t1;
    try (solve [snorm; f_equal; rip]).

   SCase "TVar".
    lets D: maskOnVar_TCon1_cases d t (TVar n).
    inverts D.

    SSCase "maskOnVar matches".
     rewritess.
     apply maskOnVar_TBot_cases in H0. subst.
     simpl.
      assert (nat_compare n (S (d' + n)) = Lt).
       rewrite <- nat_compare_lt. omega.
      rewritess.
      have (n < (S (d' + n))) by omega.
      unfold maskOnVar. 
      snorm. omega.

     SSCase "maskOnVar does not match".
      rewritess.
      set     (X := maskOnVar d (TVar n)).
      rrwrite ( substTT (S (d' + d)) (maskOnVar d t2) (TCon1 t X)
              = TCon1 t (substTT (S (d' + d)) (maskOnVar d t2) X)).
      subst X.
      rrwrite (S (d' + d) = 1 + d' + d).
      rewrite <- IHt1; auto. clear IHt1.

      lets F: substTT_TVar_cases (1 + d' + d) n t2.
      inverts F.

       SSSCase "substTT matches".
        rip. rewritess.
        eapply maskOnVar_nomatch; auto.

       inverts H1.
       SSSCase "substTT lowers var". 
        rip. rewrite H1.
        have (d <> n - 1) by omega.
        have (TVar d <> TVar (n - 1)) by congruence.
        apply maskOnVar_nomatch; auto.

       SSSCase "substTT preserves var".
        rip. rewritess. auto. 
Qed.


Lemma mask_liftTT_id
 :  forall d t
 ,  maskOnVar d (liftTT 1 d t) = liftTT 1 d t.
Proof.
 intros. gen d.
 induction t; 
  try (solve [repeat (snorm; try rewritess)]).

 Case "TCon1".
  snorm.
  destruct t0;
   try (solve [snorm; rewritess; auto]).
 
   SCase "TVar".
    repeat (unfold liftTT; unfold maskOnVar; snorm; omega).
Qed.


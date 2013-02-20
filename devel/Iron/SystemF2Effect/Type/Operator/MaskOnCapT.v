
Require Import Iron.SystemF2Effect.Type.Operator.LiftTT.
Require Import Iron.SystemF2Effect.Type.Operator.SubstTT.
Require Import Iron.SystemF2Effect.Type.KiJudge.
Require Import Iron.SystemF2Effect.Type.Exp.


(* Mask effects on the given region, 
   replacing with the bottom effect. *)
Fixpoint maskOnCapT (p : nat -> bool) (e : ty) : ty
 := match e with
    |  TVar tc       => TVar tc
    |  TForall k t1  => TForall k (maskOnCapT p t1)
    |  TApp t1 t2    => TApp (maskOnCapT p t1) (maskOnCapT p t2)
    |  TSum t1 t2    => TSum (maskOnCapT p t1) (maskOnCapT p t2)
    |  TBot k        => TBot k

    |  TCon0 tc      => TCon0 tc

    |  TCon1 tc t1
    => match t1 with
       | TCap (TyCapRegion n) 
       => if p n
             then TBot KEffect 
             else TCon1 tc (maskOnCapT p t1)

       | _ =>     TCon1 tc (maskOnCapT p t1)
       end
    
    | TCon2 tc t1 t2 => TCon2 tc (maskOnCapT p t1) (maskOnCapT p t2)

    | TCap  tc       => TCap tc
    end.
Arguments maskOnCapT p e : simpl nomatch.


(********************************************************************)
(* Helper Lemmas *)
Lemma maskOnCapT_TBot_cases
 :  forall p tc n
 ,  maskOnCapT p (TCon1 tc (TCap (TyCapRegion n))) = TBot KEffect 
 -> p n = true.
Proof.
 intros.
 unfold maskOnCapT in H.
 break (p n).
  auto. nope.
Qed.


Lemma maskOnCapT_TCon1_cases
 :   forall p tc t
 ,   maskOnCapT p (TCon1 tc t) = TBot KEffect
 \/  maskOnCapT p (TCon1 tc t) = TCon1 tc (maskOnCapT p t).
Proof.
 intros. 
 destruct t; simpl; rip.
 unfold maskOnCapT.
  destruct t. snorm.
Qed.


Lemma maskOnCapT_nomatch
 : forall p tc t2
 ,  (forall n, t2 = TCap (TyCapRegion n) -> p n = false)
 -> maskOnCapT p (TCon1 tc t2)    = TCon1 tc (maskOnCapT p t2).
Proof.
 intros.
 destruct t2; snorm.
 
 Case "TCap".
  unfold maskOnCapT.
  destruct t.
  break (p n).
   spec H n. 
    have (TCap (TyCapRegion n) = TCap (TyCapRegion n)).
    rip. congruence.
   auto.
Qed.


(********************************************************************)
Lemma maskOnCapT_kind
 :  forall ke sp t k p
 ,  KIND ke sp t k 
 -> KIND ke sp (maskOnCapT p t) k.
Proof.
 intros. gen ke sp k.
 induction t; intros; inverts_kind; simpl; auto.

 Case "TApp".
  apply IHt1 in H5. 
  apply IHt2 in H7. 
  eapply KiApp; eauto.

 Case "TCon1".
  apply IHt in H6.
  destruct t0; simpl in *; eauto.

  SCase "TCap".
   destruct t0. 
    unfold maskOnCapT. 
    split_if.
     destruct t; simpl in *.
      inverts H4. auto.
      inverts H4. auto.
      inverts H4. auto.

     destruct t; simpl in *;
      inverts H4; eapply KiCon1; simpl; eauto.

 Case "TCon2".
  spec IHt1 H5.
  spec IHt2 H7.
  eapply KiCon2; eauto.
   destruct tc; destruct t1; norm.
Qed.


Lemma maskOnCapT_liftTT
 :  forall r d t
 ,  maskOnCapT r (liftTT 1 d t) = liftTT 1 d (maskOnCapT r t).
Proof.
 intros. gen r d.
 induction t; intros; 
   try (solve [simpl; f_equal; burn]).

 Case "TCon1".
  simpl. 
  destruct t0;
   try (solve [simpl in *; try rewritess; snorm]).

   SCase "TCap". 
    simpl.
    destruct t0.
     unfold maskOnCapT. 
     snorm.
Qed.


Lemma maskOnCapT_substTT
 : forall p d t1 t2
 ,  (forall n, t2 = TCap (TyCapRegion n) -> p n = false)
 -> maskOnCapT p (substTT d t2 t1) 
 =  substTT    d (maskOnCapT p t2) (maskOnCapT p t1).
Proof. 
 intros. gen p d t2. 
 induction t1; intros;
  try (solve [snorm; f_equal; rewritess; auto]).

 Case "TForall".
  snorm. f_equal. 
  rewritess. 
   rewrite maskOnCapT_liftTT. auto.
   unfold not in *. intros.
    eapply H.
    eapply liftTT_TCap; eauto.

 Case "TCon1".
  simpl.
  destruct t1;
   try (solve [snorm; f_equal; rip]).

   SCase "TVar".
    lets D: substTT_TVar_cases d n t2.
    inverts D. 

    SSSCase "substTT matches".
     rip. rewritess. simpl. norm.
      apply maskOnCapT_nomatch. auto.
      omega. omega.

    inverts H0.
    SSSCase "substTT lowers var".
     rip. rewritess.
     simpl. 
     norm; subst; omega.

    SSSCase "substTT preserves var".
     rip. rewritess. simpl. 
     norm; subst; omega.

   SCase "TCap".
    lets D: maskOnCapT_TCon1_cases p t (TCap t0).
    inverts D.

    SSCase "maskOnCapT matches".
     destruct t0.
     rewritess.
     lets D: maskOnCapT_TBot_cases p t n. 
      rip.

    SSCase "maskOnCapT doesn't match".
     rip. rewritess. eauto.
Qed.


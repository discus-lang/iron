
Require Import Iron.SystemF2Effect.Type.Ty.
Require Import Iron.SystemF2Effect.Type.LiftTT.
Require Import Iron.SystemF2Effect.Type.SubstTT.
Require Import Iron.SystemF2Effect.Type.KiJudge.


(* Mask effects on the given region, 
   replacing with the bottom effect. *)
Fixpoint maskOnCap (r : nat) (e : ty) : ty
 := match e with
    |  TVar tc       => TVar tc
    |  TForall k t1  => TForall k (maskOnCap r t1)
    |  TApp t1 t2    => TApp (maskOnCap r t1) (maskOnCap r t2)
    |  TSum t1 t2    => TSum (maskOnCap r t1) (maskOnCap r t2)
    |  TBot k        => TBot k

    |  TCon0 tc      => TCon0 tc

    |  TCon1 tc t1
    => match t1 with
       | TCap (TyCapRegion n') 
       => if beq_nat r n' 
             then TBot KEffect 
             else TCon1 tc (maskOnCap r t1)

       | _ =>     TCon1 tc (maskOnCap r t1)
       end
    
    | TCon2 tc t1 t2 => TCon2 tc (maskOnCap r t1) (maskOnCap r t2)

    | TCap  tc       => TCap tc
    end.
Arguments maskOnCap r e : simpl nomatch.


(********************************************************************)
(* Helper Lemmas *)
Lemma maskOnCap_TBot_cases
 :  forall d tc n
 ,  maskOnCap d (TCon1 tc (TCap (TyCapRegion n))) = TBot KEffect 
 -> d = n.
Proof.
 intros.
 unfold maskOnCap in H.
 break (beq_nat d n).
  norm_beq_nat. auto.
  nope.
Qed.


Lemma maskOnCap_TCon1_cases
 :   forall d tc t
 ,   maskOnCap d (TCon1 tc t) = TBot KEffect
 \/  maskOnCap d (TCon1 tc t) = TCon1 tc (maskOnCap d t).
Proof.
 intros. 
 destruct t; simpl; rip.
 unfold maskOnCap.
  destruct t. snorm.
Qed.


Lemma maskOnCap_nomatch
 : forall n tc t2
 ,  t2 <> TCap (TyCapRegion n)
 -> maskOnCap n (TCon1 tc t2)    = TCon1 tc (maskOnCap n t2).
Proof.
 intros.
 destruct t2; snorm.
 
 Case "TCap".
  unfold maskOnCap.
  destruct t. norm. congruence.
Qed.


(********************************************************************)
Lemma maskOnCap_kind
 :  forall ke sp t k n
 ,  KIND ke sp t k 
 -> KIND ke sp (maskOnCap n t) k.
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
    unfold maskOnCap. split_if.

     norm_beq_nat. subst. inverts_kind.
     destruct t; simpl in *.
      inverts H4. auto.
      inverts H4. auto.
      inverts H4. auto.

     norm_beq_nat. inverts_kind.
     destruct t; simpl in *; inverts H4; eapply KiCon1; simpl; eauto.

 Case "TCap".
  spec IHt1 H5.
  spec IHt2 H7.
  eapply KiCon2; eauto.
   destruct tc; destruct t1; norm.
Qed.


Lemma maskOnCap_liftTT
 :  forall r d t
 ,  maskOnCap r (liftTT 1 d t) = liftTT 1 d (maskOnCap r t).
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
     unfold maskOnCap. 
     snorm.
Qed.


Lemma maskOnCap_substTT
 : forall n d t1 t2
 ,  t2 <> TCap (TyCapRegion n)
 -> maskOnCap n (substTT d t2 t1) 
 =  substTT d (maskOnCap n t2) (maskOnCap n t1).
Proof. 
 intros. gen n d t2. 
 induction t1; intros;
  try (solve [snorm; f_equal; rewritess; auto]).

 Case "TForall".
  snorm. f_equal. 
  rewritess. 
   rewrite maskOnCap_liftTT. auto.
   unfold not in *. intros.
    eapply H.
    eapply liftTT_TCap; eauto.

 Case "TCon1".
  simpl.
  destruct t1;
   try (solve [snorm; f_equal; rip]).

   SCase "TVar".
    lets D: substTT_TVar_cases d n0 t2.
    inverts D. 

    SSSCase "substTT matches".
     rip. rewritess. simpl. norm.
      apply maskOnCap_nomatch. auto.
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
    lets D: maskOnCap_TCon1_cases n t (TCap t0).
    inverts D.

    SSCase "maskOnCap matches".
     destruct t0.
     rewritess.
     lets D: maskOnCap_TBot_cases n t n0. 
      rip.

    SSCase "maskOnCap doesn't match".
     rip. rewritess. eauto.
Qed.


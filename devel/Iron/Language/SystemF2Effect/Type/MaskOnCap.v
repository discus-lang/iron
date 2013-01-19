
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Lift.
Require Import Iron.Language.SystemF2Effect.Type.KiJudge.


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


Lemma liftTT_maskOnCap
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




Require Import Iron.SystemF2Effect.Type.Operator.LiftTT.
Require Import Iron.SystemF2Effect.Type.Operator.FreeTT.
Require Import Iron.SystemF2Effect.Type.Relation.WfT.
Require Import Iron.SystemF2Effect.Type.Exp.


(* Lowering of indices in types. *)
Fixpoint lowerTT (d: nat) (tt: ty) : option ty 
 := match tt with
    |  TVar ix
    => match nat_compare ix d with
       | Eq                  => None
       | Gt                  => Some (TVar (ix - 1))
       | _                   => Some (TVar  ix)
       end

    |  TForall k t 
    => match lowerTT (S d) t with
        | Some t2            => Some (TForall k t2)
        | _                  => None
       end

  
    |  TApp t1 t2
    => match lowerTT d t1, lowerTT d t2 with
        | Some t1', Some t2' => Some (TApp t1' t2')
        | _, _               => None
       end

    |  TSum t1 t2
    => match lowerTT d t1, lowerTT d t2 with
        | Some t1', Some t2' => Some (TSum t1' t2')
        | _, _               => None
       end

    |  TBot k                => Some (TBot k)

    |  TCon0 tc              => Some (TCon0 tc)

    |  TCon1 tc t1
    => match lowerTT d t1 with
       | Some t1'            => Some (TCon1 tc t1')
       | _                   => None
       end

    |  TCon2 tc t1 t2
    => match lowerTT d t1, lowerTT d t2 with
       | Some t1', Some t2'  => Some (TCon2 tc t1' t2')
       | _, _                => None
       end

    |  TCap _                => Some tt
    end.


Ltac burn_lowerTT t := 
  induction t;
  first [ solve [snorm; f_equal; try omega]
        | solve [repeat (snorm; f_equal; eauto; rewritess; nope) ]].


Lemma lowerTT_liftTT_some
 : forall t d d'
 , lowerTT d (liftTT 1 (1 + d + d') (liftTT 1 d t)) 
 = Some (liftTT 1 (d + d') t).
Proof.
 intros. gen d. burn_lowerTT t.
Qed.
Hint Resolve lowerTT_liftTT_some.
Hint Rewrite lowerTT_liftTT_some : global.


Lemma lowerTT_some_liftTT
 :  forall d t1 t2 
 ,  lowerTT   d t1 = Some t2
 -> liftTT  1 d t2 = t1.
Proof.
 intros. gen d t2. burn_lowerTT t1.
Qed.
Hint Resolve lowerTT_some_liftTT.
Hint Rewrite lowerTT_some_liftTT : global.


Lemma lowerTT_liftTT_succ
 : forall d t1 t2
 ,  lowerTT 0 t1                    = Some t2
 -> lowerTT 0 (liftTT 1 (1 + d) t1) = Some (liftTT 1 d t2).
Proof.
 intros.
 eapply lowerTT_some_liftTT in H. subst.
 eapply lowerTT_liftTT_some.
Qed.
Hint Resolve lowerTT_liftTT_succ.
Hint Rewrite lowerTT_liftTT_succ : global.


Lemma lowerTT_liftTT
 : forall d t
 , lowerTT d (liftTT 1 d t) = Some t.
Proof.
 intros. gen d. burn_lowerTT t.
Qed.
Hint Resolve lowerTT_liftTT.
Hint Rewrite lowerTT_liftTT : global.


Lemma lowerTT_liftTT_switch
 : forall d t
 , lowerTT d (liftTT 1 (S d) (liftTT 1 d t)) 
 = Some (liftTT 1 d t).
Proof.
 intros. gen d. burn_lowerTT t.
Qed.  
Hint Resolve lowerTT_liftTT_switch.
Hint Rewrite lowerTT_liftTT_switch : global.


Lemma lowerTT_wfT_down
 :  forall n d t1 t2
 ,  d < S n
 -> WfT (S n) t1
 -> lowerTT d t1 = Some t2
 -> WfT n     t2.
Proof.
 intros. gen n d t2.
 induction t1; intros;
  try (solve [inverts H0; snorm; eauto]).

 - Case "TVar".
   snorm.
   eapply WfT_TVar. omega.
   eapply WfT_TVar. inverts H0. omega.

 - Case "TForall".
   snorm.
   + eapply WfT_TForall.
     inverts H0.
     eapply IHt1 with (n := S n) (d := S d).
      auto. omega. auto.
   + congruence.
Qed.


Lemma lowerTT_closing
 :  forall t1 t2
 ,  WfT 1 t1
 -> lowerTT 0 t1 = Some t2
 -> ClosedT t2.
Proof.
 intros.
 eapply lowerTT_wfT_down
  with (t1 := t1) (n := 0) (d := 0); eauto.
Qed.


Lemma lowerTT_wfT
 :  forall  n d t1 t2 
 ,  n <= d
 -> WfT     n t1
 -> lowerTT d t1 = Some t2
 -> t2 = t1.
Proof.
 intros. gen n d t2.
 induction t1; intros.
 - Case "TVar".
   inverts H0.
   snorm. omega.

 - Case "TForall".
   snorm.
   + inverts H0.
     assert (t = t1).
     eapply IHt1 with (n := (S n)) (d := (S d)).
      eauto.
      omega.
      auto. 
      subst. auto.
   + congruence.

 - Case "TApp".
   inverts H0.
   snorm. 
   + assert (t  = t1_1). eauto.
     assert (t0 = t1_2). eauto. 
     subst. auto.
   + congruence.
   + congruence.
    
 - Case "TSum".
   inverts H0.
   snorm. 
   + assert (t  = t1_1). eauto.
     assert (t0 = t1_2). eauto. 
     subst. auto.
   + congruence.
   + congruence.

 - Case "TBot". 
   snorm.

 - Case "TCon0". 
   snorm. 

 - Case "TCon1". 
   inverts H0.
   snorm.
   + assert (t0 = t1). eauto.
     subst. auto.
   + congruence.

 - Case "TCon2".
   inverts H0.
   snorm.
   + assert (t0 = t1_1). eauto.
     assert (t1 = t1_2). eauto.
     subst. auto.
   + congruence.
   + congruence.

 - Case "TCap".
   snorm.
Qed.


Lemma lowerTT_closedT
 :  forall t1 t2
 ,  ClosedT t1
 -> lowerTT 0 t1 = Some t2
 -> t2 = t1.
Proof.
 intros.
 eapply lowerTT_wfT with (n := 0) (d := 0); eauto.
Qed.


Lemma lowerTT_freeT
 :  forall n t1 t2
 ,  lowerTT n t1 = Some t2
 -> freeTT n t1  = false.
Proof.
 intros. gen n t2.
 induction t1; intros; eauto.
 - Case "TVar".
   snorm. 
    eapply beq_nat_false_iff. omega.
    eapply beq_nat_false_iff. omega.

 - Case "TForall".
   snorm. eauto. congruence. 

 - Case "TApp".
   snorm.
   erewrite IHt1_1; eauto.
   erewrite IHt1_2; eauto.
   congruence. congruence.

 - Case "TSum".
   snorm.
   erewrite IHt1_1; eauto.
   erewrite IHt1_2; eauto.
   congruence. congruence.

 - Case "TCon1".
   snorm.
   erewrite IHt1; eauto.
   congruence.
 
 - Case "TCon2".
   snorm.
   erewrite IHt1_1; eauto.
   erewrite IHt1_2; eauto.
   congruence. congruence.
Qed.
Hint Resolve lowerTT_freeT.   


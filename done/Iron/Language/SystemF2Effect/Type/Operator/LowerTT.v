
Require Import Iron.Language.SystemF2Effect.Type.Operator.LiftTT.
Require Import Iron.Language.SystemF2Effect.Type.Relation.FreeT.
Require Import Iron.Language.SystemF2Effect.Type.Relation.WfT.
Require Import Iron.Language.SystemF2Effect.Type.Exp.


(********************************************************************)
(* Lowering of indices in types.
   If a variable with the given index is not used in a type, 
   then we can lower all variables which have higher indices. 

   If we find a variable with the provided index, then we can't
   perform the lowering, so return None. 
*) 
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
  first [ solve [snorm; try f_equal; try congruence; omega]
        | solve [repeat (snorm; f_equal; eauto; rewritess; nope) ]].


(********************************************************************)
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

 - Case "TForall".
   snorm.
   + eapply WfT_TForall.
     inverts H0.
     eapply IHt1 with (n := S n) (d := S d).
      auto. omega. auto.
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


(* Lowering a type at an index higher than any index being used
   is identity. *)
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

 - Case "TApp".
   inverts H0.
   snorm. 
   + assert (t  = t1_1). eauto.
     assert (t0 = t1_2). eauto. 
     subst. auto.
    
 - Case "TSum".
   inverts H0.
   snorm. 
   + assert (t  = t1_1). eauto.
     assert (t0 = t1_2). eauto. 
     subst. auto.

 - Case "TBot". 
   snorm.

 - Case "TCon0". 
   snorm. 

 - Case "TCon1". 
   inverts H0.
   snorm.
   + assert (t0 = t1). eauto.
     subst. auto.

 - Case "TCon2".
   inverts H0.
   snorm.
   + assert (t0 = t1_1). eauto.
     assert (t1 = t1_2). eauto.
     subst. auto.

 - Case "TCap".
   snorm.
Qed.


(* Lowering a closed type is identity. *)
Lemma lowerTT_closedT
 :  forall t1 t2
 ,  ClosedT t1
 -> lowerTT 0 t1 = Some t2
 -> t2 = t1.
Proof.
 intros.
 eapply lowerTT_wfT with (n := 0) (d := 0); eauto.
Qed.


(* If we can lower a type at a given index, then that index did not 
   appear in the type, and the variable with that index was not free. *)
Lemma lowerTT_freeT
 :  forall n t1 t2
 ,  lowerTT n t1  = Some t2
 -> ~(FreeT n t1).
Proof.
 intros. gen n t2.
 induction t1; intros; eauto 4.
 - Case "TVar".
   snorm; omega.

 - Case "TForall".
   snorm. eauto.

 - Case "TApp".
   snorm. unfold not. intros.
   inverts H.
   + cut (~FreeT n t1_1); eauto.
   + cut (~FreeT n t1_2); eauto.

 - Case "TSum".
   snorm. unfold not. intros.
   inverts H.
   + cut (~FreeT n t1_1); eauto.
   + cut (~FreeT n t1_2); eauto.

 - Case "TCon1".
   snorm. eauto.
 
 - Case "TCon2".
   snorm. unfold not. intros.
   inverts H.
   + cut (~FreeT n t1_1); eauto.
   + cut (~FreeT n t1_2); eauto.
Qed.
Hint Resolve lowerTT_freeT.   


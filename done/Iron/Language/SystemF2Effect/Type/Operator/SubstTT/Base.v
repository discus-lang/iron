
Require Export Iron.Language.SystemF2Effect.Type.Exp.
Require Export Iron.Language.SystemF2Effect.Type.Operator.LiftTT.
Require Export Iron.Language.SystemF2Effect.Type.Operator.LowerTT.
Require Export Iron.Language.SystemF2Effect.Type.Relation.WfT.


(********************************************************************)
(* Substitution of Types in Types. *)
Fixpoint substTT (d: nat) (u: ty) (tt: ty) : ty 
 := match tt with
    | TVar ix
    => match nat_compare ix d with
       | Eq          => u
       | Gt          => TVar (ix - 1)
       | _           => TVar  ix
       end

    |  TForall k t   => TForall k (substTT (S d) (liftTT 1 0 u) t)
    |  TApp t1 t2    => TApp      (substTT d u t1) (substTT d u t2)
    |  TSum t1 t2    => TSum      (substTT d u t1) (substTT d u t2)
    |  TBot k        => TBot k

    | TCon0 tc       => TCon0 tc
    | TCon1 tc t1    => TCon1 tc  (substTT d u t1)
    | TCon2 tc t1 t2 => TCon2 tc  (substTT d u t1) (substTT d u t2)
    | TCap _         => tt
  end.


(********************************************************************)
(* What might happen when we substitute for a variable.
   This can be easier use than the raw substTT definition. *)
Lemma substTT_TVar_cases
 :  forall n1 n2 t1
 ,  (substTT n1 t1 (TVar n2) = t1            /\ n1 = n2)
 \/ (substTT n1 t1 (TVar n2) = TVar (n2 - 1) /\ n1 < n2)
 \/ (substTT n1 t1 (TVar n2) = TVar n2       /\ n1 > n2).
Proof.
 intros.
 unfold substTT.
  lift_cases; burn.
Qed. 


Lemma substTT_wfT_above
 :  forall d ix t t2
 ,  WfT d t
 -> substTT (d + ix) t2 t = t.
Proof.
 intros. gen d ix t2.
 induction t; rip; inverts H; simpl; f_equal; burn.

 Case "TVar".
  norm; omega.
  lets D: IHt H1. burn.
Qed.
Hint Resolve substTT_wfT_above.


Lemma substTT_wfT
 :  forall d ix t1 t2
 ,  ix <= d
 -> WfT (S d) t1
 -> WfT d     t2
 -> WfT d (substTT ix t2 t1).
Proof.
 intros. gen d ix t2.
 induction t1; rip; inverts H0; simpl; snorm.
Qed.
Hint Resolve substTT_wfT.


(* Closing substitution of types in types *)
Lemma substTT_closing
 :  forall t1 t2
 ,  WfT 1 t1
 -> ClosedT t2
 -> ClosedT (substTT 0 t2 t1).
Proof. eauto. Qed.
Hint Resolve substTT_closing.


Lemma substTT_closedT_id
 :  forall d t t2
 ,  ClosedT t
 -> substTT d t2 t = t.
Proof.
 intros. rrwrite (d = d + 0). eauto.
Qed.
Hint Resolve substTT_closedT_id.


Lemma substTT_liftTT_wfT1
 :  forall t1 t2
 ,  WfT 1 t1
 -> ClosedT t2
 -> substTT 0 t2 t1 = liftTT 1 0 (substTT 0 t2 t1).
Proof.
 intros.
 have    (ClosedT (substTT 0 t2 t1)).
 rrwrite (liftTT 1 0 (substTT 0 t2 t1) = substTT 0 t2 t1).
 trivial.
Qed.
Hint Resolve substTT_liftTT_wfT1.


(* Substituting into TBot is still TBot. *)
Lemma substTT_TBot
 : forall d t2 k
 , substTT d t2 (TBot k) = TBot k.
Proof. burn. Qed.
Hint Resolve substTT_TBot.
Hint Rewrite substTT_TBot : global.


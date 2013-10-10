
Require Export Iron.Language.SystemF2Effect.Type.Exp.
Require Export Iron.Language.SystemF2Effect.Type.Relation.KindT.


Inductive JoinT : nat -> nat -> ty -> ty -> Prop :=
 | JoinTVar
   :  forall p1 p2 n
   ,  JoinT  p1 p2 (TVar n) (TVar n)

 | JoinTForall
   :  forall p1 p2 k t1 t2
   ,  JoinT  p1 p2 t1 t2
   -> JoinT  p1 p2 (TForall k t1) (TForall k t2)

 | JoinTApp
   :  forall p1 p2 t11 t12 t21 t22
   ,  JoinT  p1 p2 t11 t21
   -> JoinT  p1 p2 t12 t22
   -> JoinT  p1 p2 (TApp t11 t12) (TApp t21 t22)

 | JoinTSum
   :  forall p1 p2 t11 t12 t21 t22
   ,  JoinT  p1 p2 t11 t21
   -> JoinT  p1 p2 t12 t22
   -> JoinT  p1 p2 (TSum t11 t12) (TSum t21 t22)

 | JoinTBot
   :  forall p1 p2 k
   ,  JoinT  p1 p2 (TBot k)       (TBot k)

 | JoinTCon0
   :  forall p1 p2 tc0
   ,  JoinT  p1 p2 (TCon0 tc0)    (TCon0 tc0)

 | JoinTCon1
   :  forall p1 p2 tc1 t11 t21
   ,  JoinT  p1 p2 t11 t21
   -> JoinT  p1 p2 (TCon1 tc1 t11) (TCon1 tc1 t21)

 | JoinTCon2
   :  forall p1 p2 tc2 t11 t12 t21 t22
   ,  JoinT  p1 p2 t11 t21
   -> JoinT  p1 p2 t12 t22
   -> JoinT  p1 p2 (TCon2 tc2 t11 t12) (TCon2 tc2 t21 t22)

 | JoinTCap
   :  forall p1 p2 tc
   ,  JoinT  p1 p2 (TCap tc) (TCap tc)

 | JoinTCapRgn
   :  forall p1 p2 
   ,  JoinT  p1 p2 (TCap (TyCapRegion p1)) (TCap (TyCapRegion p2)).

Hint Constructors JoinT.


(* Invert all hypothesis that are compounds join statements. *)
Ltac inverts_joinT  :=
 repeat (try 
  (match goal with 
   | [H: JoinT _ _ _ (TVar    _)      |- _ ] => inverts H
   | [H: JoinT _ _ _ (TForall _ _)    |- _ ] => inverts H
   | [H: JoinT _ _ _ (TApp    _ _)    |- _ ] => inverts H
   | [H: JoinT _ _ _ (TSum    _ _)    |- _ ] => inverts H
   | [H: JoinT _ _ _ (TBot    _)      |- _ ] => inverts H
   | [H: JoinT _ _ _ (TCon0   _)      |- _ ] => inverts H
   | [H: JoinT _ _ _ (TCon1   _ _)    |- _ ] => inverts H
   | [H: JoinT _ _ _ (TCon2   _ _ _)  |- _ ] => inverts H
   | [H: JoinT _ _ _ (TCap    _)      |- _ ] => inverts H
   end)).


Lemma joinT_refl
 :  forall p1 p2 t
 ,  JoinT  p1 p2 t t.
Proof.
 intros. induction t; eauto.
Qed.
Hint Resolve joinT_refl.


Lemma joinT_kindT_left
 :  forall p1 p2 ke sp t1 t2 k
 ,  In (SRegion p1) sp
 -> JoinT  p1 p2 t1 t2
 -> KindT  ke sp t2 k
 -> KindT  ke sp t1 k.
Proof.
 intros. gen ke k.
 induction H0; intros; inverts_kind; eauto.

 - Case "TCon2".
   destruct tc.
   destruct tc2.
   snorm. eauto.
Qed.
Hint Resolve joinT_kindT_left.


Lemma joinT_kindT_right
 :  forall p1 p2 ke sp t1 t2 k
 ,  In (SRegion p2) sp
 -> JoinT  p1 p2 t1 t2
 -> KindT  ke sp t1 k
 -> KindT  ke sp t2 k.
Proof.
 intros. gen ke k.
 induction H0; intros; inverts_kind; eauto.

 - Case "TCon2".
   destruct tc.
   destruct tc2.
   snorm. eauto.
Qed.
Hint Resolve joinT_kindT_right.



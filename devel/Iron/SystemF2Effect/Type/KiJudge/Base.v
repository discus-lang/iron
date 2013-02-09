
Require Export Iron.SystemF2Effect.Store.Prop.
Require Export Iron.SystemF2Effect.Type.Operator.LiftTT.
Require Export Iron.SystemF2Effect.Type.Predicate.Wf.
Require Export Iron.SystemF2Effect.Type.Exp.


(* Only types of effect and closure kinds can be used in sums. *)
Definition sumkind (k : ki) : Prop
 := k = KEffect.
Hint Unfold sumkind.


(* Region kinds cannot be the result of type applications. *)
Definition appkind (k : ki) : Prop
 := ~ (k = KRegion).
Hint Unfold appkind.


(* Kinds judgement assigns a kind to a type *)
Inductive KIND : kienv -> stprops -> ty -> ki -> Prop :=
  | KiVar
    :  forall ke sp i k
    ,  get i ke = Some k
    -> KIND ke sp (TVar i) k

  | KiForall
    :  forall ke sp k t
    ,  KIND (ke :> k) sp t KData
    -> KIND ke        sp (TForall k t) KData

  | KiApp 
    :  forall ke sp t1 t2 k11 k12
    ,  appkind k12
    -> KIND ke sp t1 (KFun k11 k12)
    -> KIND ke sp t2 k11
    -> KIND ke sp (TApp t1 t2) k12

  | KiSum
    :  forall ke sp k t1 t2
    ,  sumkind k
    -> KIND ke sp t1 k -> KIND ke sp t2 k
    -> KIND ke sp (TSum t1 t2) k

  | KiBot
    :  forall ke sp k
    ,  sumkind k
    -> KIND ke sp (TBot k) k

  | KiCon0
    :  forall ke sp tc k
    ,  k = kindOfTyCon0 tc
    -> KIND ke sp (TCon0 tc) k

  | KiCon1 
    :  forall ke sp tc t1 k1 k
    ,  KFun k1 k = kindOfTyCon1 tc
    -> KIND ke sp t1 k1
    -> KIND ke sp (TCon1 tc t1) k

  | KiCon2 
    :  forall ke sp tc t1 t2 k1 k2 k
    ,  KFun k1 (KFun k2 k) = kindOfTyCon2 tc
    -> KIND ke sp t1 k1
    -> KIND ke sp t2 k2
    -> KIND ke sp (TCon2 tc t1 t2) k

  | KiCap
    :  forall ke sp n
    ,  In (SRegion n) sp
    -> KIND ke sp (TCap (TyCapRegion n)) KRegion.

Hint Constructors KIND.


(********************************************************************)
(* Invert all hypothesis that are compound kinding statements. *)
Ltac inverts_kind :=
 repeat 
  (match goal with 
   | [ H: KIND _ _ (TVar _)      _  |- _ ] => inverts H
   | [ H: KIND _ _ (TForall _ _) _  |- _ ] => inverts H
   | [ H: KIND _ _ (TApp _ _)    _  |- _ ] => inverts H
   | [ H: KIND _ _ (TSum _ _)    _  |- _ ] => inverts H
   | [ H: KIND _ _ (TBot _ )     _  |- _ ] => inverts H
   | [ H: KIND _ _ (TCon0 _)     _  |- _ ] => inverts H
   | [ H: KIND _ _ (TCon1 _ _)   _  |- _ ] => inverts H
   | [ H: KIND _ _ (TCon2 _ _ _) _  |- _ ] => inverts H
   | [ H: KIND _ _ (TCap _)      _  |- _ ] => inverts H
   end).


(********************************************************************)
(* Forms of types *)
Lemma kind_region
 :  forall t sp
 ,  KIND nil sp t KRegion
 -> (exists n, t = TCap (TyCapRegion n)).
Proof.
 intros.
 destruct t; burn.

  Case "TApp".
   inverts_kind.
   false. auto.

  Case "TCon0".
   destruct t; nope.

  Case "TCon1".
   destruct t; nope.

  Case "TCon2".
   destruct t1; nope.
   inverts_kind.
    destruct tc. simpl in *. nope.

  Case "TCap".
   destruct t.
   exists n. auto.
Qed.
Hint Resolve kind_region.


Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Value.Wf.
Require Export Iron.Language.SystemF2Effect.Value.Lift.


(* Store Environment holds the types of locations. *)
Definition stenv := list ty.


(* Types of Value expressions *)
Inductive TYPEV : kienv -> tyenv -> stenv -> val -> ty -> Prop := 
  | TvVar
    :  forall ke te se i t
    ,  get i te = Some t
    -> TYPEV ke te se (VVar i) t 

  | TvLoc 
    :  forall ke te se i r t
    ,  get i se  = Some (tRef r t)
    -> TYPEV ke te se (VLoc i) (tRef r t)

  | TvLam
    :  forall ke te se t1 t2 x2 e2
    ,  KIND ke t1 KData
    -> TYPEX ke (te :> t1) se x2 t2 e2
    -> TYPEV ke te se (VLam t1 x2) (tFun t1 e2 t2)

  | TvLAM
    :  forall ke te se k1 t2 x2
    ,  TYPEX (ke :> k1) (liftTE 0 te) (liftTE 0 se) x2 t2 (TBot KEffect)
    -> TYPEV ke         te            se            (VLAM k1 x2) (TForall k1 t2)

  | TvConstNat
    :  forall ke te se n
    ,  TYPEV ke te se (VConst (CNat n))  tNat

  | TvConstBool
    :  forall ke te se b
    ,  TYPEV ke te se (VConst (CBool b)) tBool


  with TYPEX : kienv -> tyenv -> stenv -> exp -> ty -> ty -> Prop :=
  | TxVal
    :  forall ke te se v1 t1
    ,  TYPEV ke te se v1        t1
    -> TYPEX ke te se (XVal v1) t1 (TBot KEffect)

  | TxLet
    :  forall ke te se t1 x1 t2 x2 e1 e2
    ,  KIND  ke t1 KData
    -> TYPEX ke te         se x1 t1 e1
    -> TYPEX ke (te :> t1) se x2 t2 e2
    -> TYPEX ke te         se (XLet t1 x1 x2) t2 (TSum e1 e2)

  | TxApp
    :  forall ke te se t11 t12 v1 v2 e1
    ,  TYPEV ke te se v1 (tFun t11 e1 t12) 
    -> TYPEV ke te se v2 t11
    -> TYPEX ke te se (XApp v1 v2) t12 e1

  | TvAPP
    :  forall ke te se v1 k11 t12 t2
    ,  TYPEV ke te se v1 (TForall k11 t12)
    -> KIND  ke t2 k11
    -> TYPEX ke te se (XAPP v1 t2) (substTT 0 t2 t12) (TBot KEffect)

  (* Store Operators *)
  | TxNew
    :  forall ke te se x t tL e eL
    ,  lowerTT 0 t = Some tL
    -> lowerTT 0 e = Some eL
    -> TYPEX (ke :> KRegion) (liftTE 0 te) (liftTE 0 se) x        t  e
    -> TYPEX ke              te             se           (XNew x) tL eL
    (* TODO: As it stands this should be sound and go through the proof,
             but need to cut effects on new region from 'e' before lowering
             otherwise the body can't actually use the new region *)

  | TxUse
    :  forall ke te se n x t e
    ,  TYPEX ke te se x t e
    -> TYPEX ke te se (XUse n x) t e
    (* TODO: cut effects due to the bound region variable *)

  | TxOpAlloc 
    :  forall ke te se r1 v2 t2
    ,  KIND  ke r1 KRegion
    -> TYPEV ke te se v2 t2
    -> TYPEX ke te se (XAlloc r1 v2) (tRef r1 t2) (tAlloc r1)

  | TxOpRead
    :  forall ke te se v1 r1 t2
    ,  KIND  ke r1 KRegion
    -> TYPEV ke te se v1 (tRef r1 t2)
    -> TYPEX ke te se (XRead r1 v1)     t2    (tRead r1)

  | TxOpWrite
    :  forall ke te se v1 v2 r1 t2
    ,  KIND  ke r1 KRegion
    -> TYPEV ke te se v1 (tRef r1 t2)
    -> TYPEV ke te se v2 t2
    -> TYPEX ke te se (XWrite r1 v1 v2) tUnit (tWrite r1)

  (* Primtive Operators *)
  | TxOpSucc
    :  forall ke te se v1
    ,  TYPEV ke te se v1 tNat
    -> TYPEX ke te se (XOp1 OSucc v1)   tNat (TBot KEffect)

  | TxOpIsZero
    :  forall ke te se v1
    ,  TYPEV ke te se v1 tNat
    -> TYPEX ke te se (XOp1 OIsZero v1) tBool (TBot KEffect).

Hint Constructors TYPEV.
Hint Constructors TYPEX.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_type :=
 repeat 
  (match goal with 
   | [ H: TYPEV _ _ _ (VVar   _)     _      |- _ ] => inverts H
   | [ H: TYPEV _ _ _ (VLoc   _)     _      |- _ ] => inverts H
   | [ H: TYPEV _ _ _ (VLam   _ _)   _      |- _ ] => inverts H
   | [ H: TYPEV _ _ _ (VLAM   _ _)   _      |- _ ] => inverts H
   | [ H: TYPEV _ _ _ (VConst _)     _      |- _ ] => inverts H
   | [ H: TYPEX _ _ _ (XVal   _)     _ _    |- _ ] => inverts H
   | [ H: TYPEX _ _ _ (XLet   _ _ _) _ _    |- _ ] => inverts H 
   | [ H: TYPEX _ _ _ (XApp   _ _)   _ _    |- _ ] => inverts H 
   | [ H: TYPEX _ _ _ (XAPP   _ _)   _ _    |- _ ] => inverts H 
   | [ H: TYPEX _ _ _ (XNew   _) _ _        |- _ ] => inverts H
   | [ H: TYPEX _ _ _ (XUse   _ _) _ _      |- _ ] => inverts H
   | [ H: TYPEX _ _ _ (XAlloc _ _)   _ _    |- _ ] => inverts H
   | [ H: TYPEX _ _ _ (XRead  _ _)   _ _    |- _ ] => inverts H
   | [ H: TYPEX _ _ _ (XWrite _ _ _) _ _    |- _ ] => inverts H
   | [ H: TYPEX _ _ _ (XOp1   _ _)   _ _    |- _ ] => inverts H 
   end).


(********************************************************************)
(* A well typed expression is well formed *)
Theorem type_wfX
 :  forall ke te se x t e
 ,  TYPEX ke te se x t e
 -> wfX (length ke) (length te) (length se) x.
Proof.
 intros. gen ke te se t e.
 induction x using exp_mutind with 
  (PV := fun v => forall ke te se t1
      ,  TYPEV ke te se v t1
      -> wfV (length ke) (length te) (length se) v);
   rip; inverts_type; try burn.

 Case "VLam".
  spec IHx H7. burn.

 Case "VLAM".
  eapply WfV_VLAM.
  spec IHx H6.
  rrwrite (length (ke :> k) = S (length ke)) in IHx.
  rewrite <- length_liftTE in IHx.
  rewrite <- length_liftTE in IHx.
  auto.

 Case "XLet".
  spec IHx1 H9.
  spec IHx2 H10.
  burn.

 Case "XNew".
  eapply WfX_XNew.
  spec IHx H6.
  rrwrite (length (ke :> KRegion) = S (length ke)) in IHx.
  rewrite <- length_liftTE in IHx.
  rewrite <- length_liftTE in IHx.
  burn.
Qed.
Hint Resolve type_wfX.




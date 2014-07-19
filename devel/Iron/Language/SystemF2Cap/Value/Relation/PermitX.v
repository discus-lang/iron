
Require Export Iron.Language.SystemF2Cap.Type.
Require Export Iron.Language.SystemF2Cap.Value.Exp.
Require Export Iron.Language.SystemF2Cap.Value.Relation.TyJudge.

Inductive 
  (* All computations in this value are permitted to evaluate. *)
  PermitV :  kienv -> tyenv -> stenv -> stprops -> val -> Prop :=

  | PvVar
    :  forall  ke te se sp i
    ,  PermitV ke te se sp (VVar i)

  | PvLoc 
    :  forall  ke te se sp l
    ,  PermitV ke te se sp (VLoc l)

  | PvBox 
    :  forall  ke te se sp x
    ,  PermitX ke te se sp x
    -> PermitV ke te se sp (VBox x)

  | PvLam
    :  forall  ke  te se sp t x   
    ,  PermitX ke (te :> t) se sp x
    -> PermitV ke  te       se sp (VLam t x)

  | PvLAM 
    :  forall  ke te se sp k x
    ,  PermitX (ke :> (OAbs, k)) (liftTE 0 te) se sp x
    -> PermitV ke te se sp (VLAM k x)

  | PvConst
    :  forall  ke te se sp c
    ,  PermitV ke te se sp (VConst c)

 with
  (* All computations in this expression are permitted to evaluate. *)
  PermitX : kienv -> tyenv -> stenv -> stprops -> exp -> Prop :=

  | PxVal 
    :  forall  ke te se sp v
    ,  PermitV ke te se sp v
    -> PermitX ke te se sp (XVal v)

  | PxLet 
    :  forall  ke  te se sp t1 x1 x2
    ,  PermitX ke  te se sp x1 
    -> PermitX ke (te :> t1) se sp x2
    -> PermitX ke  te se sp (XLet t1 x1 x2)

  | PxApp 
    :  forall  ke te se sp v1 v2
    ,  PermitV ke te se sp v1 
    -> PermitV ke te se sp v2
    -> PermitX ke te se sp (XApp v1 v2)

  | PxAPP 
    :  forall  ke te se sp v1 t2
    ,  PermitV ke te se sp v1
    -> PermitX ke te se sp (XAPP v1 t2)

  | PxPrivate 
    :  forall  ke te se sp ts x t e ke' te'
    ,  ke' = ke :> (OCon, KRegion)
    -> te' = liftTE 0 te >< ts
    -> TypeX   ke' te' se sp x t e
    -> PermitT ke' te' e
    -> PermitX ke' te' se sp x
    -> PermitX ke  te  se sp (XPrivate ts x)

  | PxExtend
    :  forall  ke te se sp r x ke' te'
    ,  ke' = ke :> (OCon, KRegion)
    -> te' = liftTE 0 te
    -> PermitX ke' te' se sp x
    -> PermitX ke  te  se sp (XExtend r x)

  | PxRun
    :  forall  ke te se sp v e t
    ,  TypeV   ke te se sp v (TSusp e t)
    -> PermitT ke te e
    -> PermitV ke te se sp v
    -> PermitX ke te se sp (XRun v)

  | PxOpAlloc
    :  forall  ke te se sp r v
    ,  PermitV ke te se sp v
    -> PermitX ke te se sp (XAlloc r v)

  | PxOpRead
    :  forall  ke te se sp r v
    ,  PermitV ke te se sp v
    -> PermitX ke te se sp (XRead r v)

  | PxOpWrite 
    :  forall  ke te se sp r v1 v2
    ,  PermitV ke te se sp v1
    -> PermitV ke te se sp v2
    -> PermitX ke te se sp (XWrite r v1 v2)

  | PxOpPrim
    :  forall  ke te se sp op v
    ,  PermitV ke te se sp v
    -> PermitX ke te se sp (XOp1 op v).

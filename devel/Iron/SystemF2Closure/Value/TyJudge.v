
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Value.Relation.Wf.
Require Export Iron.Language.SystemF2Effect.Value.Operator.LiftX.
Require Export Iron.Language.SystemF2Effect.Store.Prop.


(* Store Environment holds the types of locations. *)
Definition stenv := list ty.


(* Types of primops. 
   We keep this separate from the main typing judgement to make it easy
   to add new primops. *)
Fixpoint typeOfOp1 (op : op1) : ty
 := match op with
    | OSucc    => TFun TNat TNat  (TBot KEffect)
    | OIsZero  => TFun TNat TBool (TBot KEffect)
    end.


(* Types of Value expressions *)
Inductive 
  TYPEV : kienv -> tyenv -> stenv -> stprops 
        -> val  -> ty    -> ty
        -> Prop := 

  (* Variables.
     We get the type of a variable from the type environment. *)
  | TvVar
    :  forall ke te se sp i t
    ,  get i te = Some t
    -> KindT  ke sp t KData
    -> TYPEV  ke te se sp (VVar i) t (TDeepUse t)

  (* Store locations.
     We get the type of a location from the store typing.
     The type of a location must be a Reference because we need somewhere
     to attach the region variable. Our primitive types don't have region
     annotations themselves. *)
  | TvLoc 
    :  forall ke te se sp i r t
    ,  get i se = Some (TRef r t)
    -> KindT  ke sp       (TRef r t) KData       
    -> TYPEV  ke te se sp
              (VLoc i) (TRef r t) (TSum KClosure (TUse r) (TDeepUse t))

  (* Value abstraction.
     The body is checked in an environment extended with the type of
     of the formal parameter. *)
  | TvLam
    :  forall ke te se sp t1 t2 x2 e2
    ,  KindT   ke sp t1 KData
    -> TYPEX  ke (te :> t1) se sp x2 t2 TPure TEmpty
    -> TYPEV  ke te         se sp (VLam t1 x2) (TFun t1 t2) TEmpty

  (* Type abstraction.
     The body is checked in an environemnt extended with the kind of
     the formal parameter. As the parameter kind is pushed onto the base
     of the kind environment we need to lift any references to kinds 
     higher in the stack across the new one. The body expression must
     be pure because we don't have anywhere to store the effect of the
     body in the type of the overall abstraction. This is different for
     value abstractions, where the function constructor has an effect 
     annotation. *) 
  | TvLAM
    :  forall ke te se sp k1 t2 x2
    ,  TYPEX (ke :> k1) (liftTE 0 te) (liftTE 0 se) sp x2 t2 TPure TEmpty
    -> TYPEV ke te se sp (VLAM k1 x2) (TForall k1 t2) TEmpty

  (* Primitive constants. 
     We get the types of these from the 'typeOfConst' function so we can
     add new sorts of constants without changing the proof. *)
  | TvConst
    :  forall ke te se sp c t
    ,  t = typeOfConst c
    -> TYPEV  ke te se sp (VConst c) t


  with TYPEX :  kienv -> tyenv -> stenv -> stprops 
             -> exp   -> ty -> ty -> ty
             -> Prop :=

  (* Embed values in the expression language.
     All values are pure because they can't be stepped further, which 
     in turn means they can't perform any more effectful actions. *)
  | TxVal
    :  forall ke te se sp v1 t1
    ,  TYPEV  ke te se sp v1 t1
    -> TYPEX  ke te se sp (XVal v1) t1 (TBot KEffect)

  (* Let-bindings. *)
  | TxLet
    :  forall ke te se sp t1 x1 t2 x2 e1 e2
    ,  KindT  ke sp t1 KData
    -> TYPEX  ke te         se sp x1 t1 e1
    -> TYPEX  ke (te :> t1) se sp x2 t2 e2
    -> TYPEX  ke te         se sp (XLet t1 x1 x2) t2 (TSum e1 e2)

  (* Value application. *)
  | TxApp
    :  forall ke te se sp t11 t12 v1 v2 e1
    ,  TYPEV  ke te se sp v1 (TFun t11 e1 t12) 
    -> TYPEV  ke te se sp v2 t11
    -> TYPEX  ke te se sp (XApp v1 v2) t12 e1

  (* Type application. *)
  | TvAPP
    :  forall ke te se sp v1 k11 t12 t2
    ,  TYPEV  ke te se sp v1 (TForall k11 t12)
    -> KindT  ke sp t2 k11
    -> TYPEX  ke te se sp (XAPP v1 t2) (substTT 0 t2 t12) (TBot KEffect)

  (* Store Operators ******************)
  (* Create a new region. *)
  | TxNew
    :  forall ke te se sp x t tL e eL
    ,  lowerTT 0 t               = Some tL
    -> lowerTT 0 (maskOnVarT 0 e) = Some eL
    -> TYPEX (ke :> KRegion) (liftTE 0 te) (liftTE 0 se) sp x        t  e
    -> TYPEX ke              te             se           sp (XNew x) tL eL

  (* Allocate a new heap binding. *)
  | TxOpAlloc 
    :  forall ke te se sp r1 v2 t2
    ,  KindT  ke sp r1 KRegion
    -> TYPEV  ke te se sp v2 t2
    -> TYPEX  ke te se sp (XAlloc r1 v2) (TRef r1 t2) (TAlloc r1)

  (* Read a value from a heap binding. *)
  | TxOpRead
    :  forall ke te se sp v1 r1 t2
    ,  KindT  ke sp r1 KRegion
    -> TYPEV  ke te se sp v1 (TRef r1 t2)
    -> TYPEX  ke te se sp (XRead r1 v1)     t2    (TRead r1)

  (* Write a value to a heap binding. *)
  | TxOpWrite
    :  forall ke te se sp v1 v2 r1 t2
    ,  KindT  ke sp r1 KRegion
    -> TYPEV  ke te se sp v1 (TRef r1 t2)
    -> TYPEV  ke te se sp v2 t2
    -> TYPEX  ke te se sp (XWrite r1 v1 v2) TUnit (TWrite r1)

  (* Primtive Operators ***************)
  | TxOpPrim
    :  forall ke te se sp op v1 t11 t12 e
    ,  typeOfOp1 op = TFun t11 t12 e
    -> TYPEV  ke te se sp v1 t11
    -> TYPEX  ke te se sp (XOp1 op v1) t12 e.

(*
  | TxCastEffect
    :  TYPEX  ke te se sp x t1 e1
    -> SubsT  ke te se sp x e2 e1          (* also use to fix equiv of effect *)
    -> TYPEX  ke te se sp x (casteff e2 t1) e2
*)
Hint Constructors TYPEV.
Hint Constructors TYPEX.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_type :=
 repeat 
  (match goal with 
   | [ H: TYPEV _ _ _ _ (VVar   _)     _    |- _ ] => inverts H
   | [ H: TYPEV _ _ _ _ (VLoc   _)     _    |- _ ] => inverts H
   | [ H: TYPEV _ _ _ _ (VLam   _ _)   _    |- _ ] => inverts H
   | [ H: TYPEV _ _ _ _ (VLAM   _ _)   _    |- _ ] => inverts H
   | [ H: TYPEV _ _ _ _ (VConst _)     _    |- _ ] => inverts H
   | [ H: TYPEX _ _ _ _ (XVal   _)     _ _  |- _ ] => inverts H
   | [ H: TYPEX _ _ _ _ (XLet   _ _ _) _ _  |- _ ] => inverts H 
   | [ H: TYPEX _ _ _ _ (XApp   _ _)   _ _  |- _ ] => inverts H 
   | [ H: TYPEX _ _ _ _ (XAPP   _ _)   _ _  |- _ ] => inverts H 
   | [ H: TYPEX _ _ _ _ (XNew   _)     _ _  |- _ ] => inverts H
   | [ H: TYPEX _ _ _ _ (XAlloc _ _)   _ _  |- _ ] => inverts H
   | [ H: TYPEX _ _ _ _ (XRead  _ _)   _ _  |- _ ] => inverts H
   | [ H: TYPEX _ _ _ _ (XWrite _ _ _) _ _  |- _ ] => inverts H
   | [ H: TYPEX _ _ _ _ (XOp1   _ _)   _ _  |- _ ] => inverts H 
   end).



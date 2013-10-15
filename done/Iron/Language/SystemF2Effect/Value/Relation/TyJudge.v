
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Value.Relation.Wf.
Require Export Iron.Language.SystemF2Effect.Value.Operator.LiftX.
Require Export Iron.Language.SystemF2Effect.Store.Prop.


(********************************************************************)
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
  TypeV : kienv -> tyenv -> stenv -> stprops 
        -> val  -> ty 
        -> Prop := 

  (* Variables.
     We get the type of a variable from the type environment. *)
  | TvVar
    :  forall ke te se sp i t
    ,  get i te = Some t
    -> KindT  ke sp t KData
    -> TypeV  ke te se sp (VVar i) t 

  (* Store locations.
     We get the type of a location from the store typing.
     The type of a location must be a Reference because we need somewhere
     to attach the region variable. Our primitive types don't have region
     annotations themselves. *)
  | TvLoc 
    :  forall ke te se sp l r t
    ,  get l se = Some (TRef r t)
    -> KindT  ke sp       (TRef r t) KData       
    -> TypeV  ke te se sp (VLoc l)   (TRef r t)

  (* Value abstraction.
     The body is checked in an environment extended with the type of
     of the formal parameter. *)
  | TvLam
    :  forall ke te se sp t1 t2 x2 e2
    ,  KindT  ke sp t1 KData
    -> TypeX  ke (te :> t1) se sp x2 t2 e2
    -> TypeV  ke te         se sp (VLam t1 x2) (TFun t1 e2 t2)

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
    ,  TypeX (ke :> k1) (liftTE 0 te) (liftTE 0 se) sp x2 t2 (TBot KEffect)
    -> TypeV ke          te            se   sp (VLAM k1 x2) (TForall k1 t2)

  (* Primitive constants. 
     We get the types of these from the 'typeOfConst' function so we can
     add new sorts of constants without changing the proof. *)
  | TvConst
    :  forall ke te se sp c t
    ,  t = typeOfConst c
    -> TypeV  ke te se sp (VConst c) t


  with TypeX :  kienv -> tyenv -> stenv -> stprops 
             -> exp   -> ty -> ty 
             -> Prop :=

  (* Embed values in the expression language.
     All values are pure because they can't be stepped further, which 
     in turn means they can't perform any more effectful actions. *)
  | TxVal
    :  forall ke te se sp v1 t1
    ,  TypeV  ke te se sp v1 t1
    -> TypeX  ke te se sp (XVal v1) t1 (TBot KEffect)

  (* Let-bindings. *)
  | TxLet
    :  forall ke te se sp t1 x1 t2 x2 e1 e2
    ,  KindT  ke sp t1 KData
    -> TypeX  ke te         se sp x1 t1 e1
    -> TypeX  ke (te :> t1) se sp x2 t2 e2
    -> TypeX  ke te         se sp (XLet t1 x1 x2) t2 (TSum e1 e2)

  (* Value application. *)
  | TxApp
    :  forall ke te se sp t11 t12 v1 v2 e1
    ,  TypeV  ke te se sp v1 (TFun t11 e1 t12) 
    -> TypeV  ke te se sp v2 t11
    -> TypeX  ke te se sp (XApp v1 v2) t12 e1

  (* Type application. *)
  | TvAPP
    :  forall ke te se sp v1 k11 t12 t2
    ,  TypeV  ke te se sp v1 (TForall k11 t12)
    -> KindT  ke sp t2 k11
    -> TypeX  ke te se sp (XAPP v1 t2) (substTT 0 t2 t12) (TBot KEffect)

  (* Store Operators ******************)
  (* Create a private region. *)
  | TxPrivate
    :  forall ke te se sp x t tL e eL
    ,  lowerTT 0 t                = Some tL
    -> lowerTT 0 (maskOnVarT 0 e) = Some eL
    -> TypeX (ke :> KRegion) (liftTE 0 te) (liftTE 0 se) sp x            t  e
    -> TypeX ke              te            se            sp (XPrivate x) tL eL

  (* Extend an existing region. *)
  | TxExtend
    :  forall ke te se sp r1 x2 t e eL
    ,  lowerTT 0 (maskOnVarT 0 e) = Some eL
    -> KindT ke sp r1 KRegion
    -> TypeX (ke :> KRegion) (liftTE 0 te) (liftTE 0 se) sp x2 t e
    -> TypeX ke te se  sp (XExtend r1 x2) (substTT 0 r1 t) (TSum eL (TAlloc r1))

  (* Allocate a new heap binding. *)
  | TxOpAlloc 
    :  forall ke te se sp r1 v2 t2
    ,  KindT  ke sp r1 KRegion
    -> TypeV  ke te se sp v2 t2
    -> TypeX  ke te se sp (XAlloc r1 v2) (TRef r1 t2) (TAlloc r1)

  (* Read a value from a heap binding. *)
  | TxOpRead
    :  forall ke te se sp v1 r1 t2
    ,  KindT  ke sp r1 KRegion
    -> TypeV  ke te se sp v1 (TRef r1 t2)
    -> TypeX  ke te se sp (XRead r1 v1)     t2    (TRead r1)

  (* Write a value to a heap binding. *)
  | TxOpWrite
    :  forall ke te se sp v1 v2 r1 t2
    ,  KindT  ke sp r1 KRegion
    -> TypeV  ke te se sp v1 (TRef r1 t2)
    -> TypeV  ke te se sp v2 t2
    -> TypeX  ke te se sp (XWrite r1 v1 v2) TUnit (TWrite r1)

  (* Primtive Operators ***************)
  | TxOpPrim
    :  forall ke te se sp op v1 t11 t12 e
    ,  typeOfOp1 op = TFun t11 t12 e
    -> TypeV  ke te se sp v1 t11
    -> TypeX  ke te se sp (XOp1 op v1) t12 e.

Hint Constructors TypeV.
Hint Constructors TypeX.


(********************************************************************)
(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_type :=
 repeat 
  (match goal with 
   | [ H: TypeV _ _ _ _ (VVar   _)     _    |- _ ] => inverts H
   | [ H: TypeV _ _ _ _ (VLoc   _)     _    |- _ ] => inverts H
   | [ H: TypeV _ _ _ _ (VLam   _ _)   _    |- _ ] => inverts H
   | [ H: TypeV _ _ _ _ (VLAM   _ _)   _    |- _ ] => inverts H
   | [ H: TypeV _ _ _ _ (VConst _)     _    |- _ ] => inverts H
   | [ H: TypeX _ _ _ _ (XVal   _)     _ _  |- _ ] => inverts H
   | [ H: TypeX _ _ _ _ (XLet   _ _ _) _ _  |- _ ] => inverts H 
   | [ H: TypeX _ _ _ _ (XApp   _ _)   _ _  |- _ ] => inverts H 
   | [ H: TypeX _ _ _ _ (XAPP   _ _)   _ _  |- _ ] => inverts H 
   | [ H: TypeX _ _ _ _ (XPrivate _)   _ _  |- _ ] => inverts H
   | [ H: TypeX _ _ _ _ (XExtend  _ _) _ _  |- _ ] => inverts H
   | [ H: TypeX _ _ _ _ (XAlloc _ _)   _ _  |- _ ] => inverts H
   | [ H: TypeX _ _ _ _ (XRead  _ _)   _ _  |- _ ] => inverts H
   | [ H: TypeX _ _ _ _ (XWrite _ _ _) _ _  |- _ ] => inverts H
   | [ H: TypeX _ _ _ _ (XOp1   _ _)   _ _  |- _ ] => inverts H 
   end).



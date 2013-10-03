
Require Export Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Type.


(********************************************************************)
(* Well formed expressions are closed under the given environment. *)
Inductive WfV (kn tn sn: nat) : val -> Prop :=
 | WfV_VVar 
   :  forall ti
   ,  ti < tn
   -> WfV kn tn sn (VVar ti)
 
 | WfV_VLoc
   :  forall li
   ,  li < sn
   -> WfV kn tn sn (VLoc li) 

 | WfV_VLam
   :  forall t1 x2
   ,  WfT kn t1 -> WfX kn (S tn) sn x2
   -> WfV kn tn sn (VLam t1 x2)

 | WfV_VLAM
   :  forall k1 x
   ,  WfX (S kn) tn sn x
   -> WfV kn tn sn (VLAM k1 x)

 | WfV_VConst
   :  forall c
   ,  WfV kn tn sn (VConst c)

with   WfX (kn tn sn: nat) : exp -> Prop :=

 | WfX_XVal
   :  forall v
   ,  WfV kn tn sn v
   -> WfX kn tn sn (XVal v)

 | WfX_XLet 
   :  forall t1 x1 x2
   ,  WfT kn t1
   -> WfX kn tn sn x1
   -> WfX kn (S tn) sn x2
   -> WfX kn tn sn (XLet t1 x1 x2) 

 | WfX_XApp 
   :  forall v1 v2
   ,  WfV kn tn sn v1 -> WfV kn tn sn v2
   -> WfX kn tn sn (XApp v1 v2)

 | WfX_VAPP
   :  forall x1 t2
   ,  WfV kn tn sn x1 -> WfT kn t2
   -> WfX kn tn sn (XAPP x1 t2)

 | WfX_XOp1
   :  forall op1 v1
   ,  WfV kn tn sn v1
   -> WfX kn tn sn (XOp1 op1 v1)

 | WfX_XPrivate
   :  forall x
   ,  WfX (S kn) tn sn x 
   -> WfX kn     tn sn (XPrivate x)

 | WfX_XExtend
   :  forall t1 x2
   ,  WfT kn t1
   -> WfX (S kn) tn sn x2
   -> WfX kn     tn sn (XExtend t1 x2)

 | WfX_XAlloc
   :  forall tR v1
   ,  WfT kn tR
   -> WfV kn tn sn v1
   -> WfX kn tn sn (XAlloc tR v1)

 | WfX_XRead
   :  forall tR v1
   ,  WfT kn tR
   -> WfV kn tn sn v1
   -> WfX kn tn sn (XRead tR v1)

 | WfX_XWrite
   :  forall tR v1 v2
   ,  WfT kn tR
   -> WfV kn tn sn v1
   -> WfV kn tn sn v2
   -> WfX kn tn sn (XWrite tR v1 v2).

Hint Constructors WfX.
Hint Constructors WfV.


(* Closed expressions are well formed under
   empty type and kind environments, but may contain store locations. *)
Notation ClosedX X := (exists sn, WfX O O sn X).


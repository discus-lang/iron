
Require Export Iron.SystemF2Effect.Value.Exp.
Require Export Iron.SystemF2Effect.Type.


(* Well formed expressions are closed under the given environment. *)
Inductive wfV (kn tn sn: nat) : val -> Prop :=
 | WfV_VVar 
   :  forall ti
   ,  ti < tn
   -> wfV kn tn sn (VVar ti)
 
 | WfV_VLoc
   :  forall li
   ,  li < sn
   -> wfV kn tn sn (VLoc li) 

 | WfV_VLam
   :  forall t1 x2
   ,  wfT kn t1 -> wfX kn (S tn) sn x2
   -> wfV kn tn sn (VLam t1 x2)

 | WfV_VLAM
   :  forall k1 x
   ,  wfX (S kn) tn sn x
   -> wfV kn tn sn (VLAM k1 x)

 | WfV_VConst
   :  forall c
   ,  wfV kn tn sn (VConst c)

with   wfX (kn tn sn: nat) : exp -> Prop :=

 | WfX_XVal
   :  forall v
   ,  wfV kn tn sn v
   -> wfX kn tn sn (XVal v)

 | WfX_XLet 
   :  forall t1 x1 x2
   ,  wfT kn t1
   -> wfX kn tn sn x1
   -> wfX kn (S tn) sn x2
   -> wfX kn tn sn (XLet t1 x1 x2) 

 | WfX_XApp 
   :  forall v1 v2
   ,  wfV kn tn sn v1 -> wfV kn tn sn v2
   -> wfX kn tn sn (XApp v1 v2)

 | WfX_VAPP
   :  forall x1 t2
   ,  wfV kn tn sn x1 -> wfT kn t2
   -> wfX kn tn sn (XAPP x1 t2)

 | WfX_XOp1
   :  forall op1 v1
   ,  wfV kn tn sn v1
   -> wfX kn tn sn (XOp1 op1 v1)

 | WfX_XNew
   :  forall x
   ,  wfX (S kn) tn sn x 
   -> wfX kn     tn sn (XNew x)

 | WfX_XAlloc
   :  forall tR v1
   ,  wfT kn tR
   -> wfV kn tn sn v1
   -> wfX kn tn sn (XAlloc tR v1)

 | WfX_XRead
   :  forall tR v1
   ,  wfT kn tR
   -> wfV kn tn sn v1
   -> wfX kn tn sn (XRead tR v1)

 | WfX_XWrite
   :  forall tR v1 v2
   ,  wfT kn tR
   -> wfV kn tn sn v1
   -> wfV kn tn sn v2
   -> wfX kn tn sn (XWrite tR v1 v2).

Hint Constructors wfX.
Hint Constructors wfV.


(* Closed expressions are well formed under
   empty type and kind environments, but may contain store locations. *)
Definition closedX (xx: exp) : Prop
 := exists sn, wfX O O sn xx.
Hint Unfold closedX.


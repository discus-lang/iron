
Require Export Iron.Language.SystemF2Data.Exp.Base.


(* Well formed expressions are closed under the given environment. *)
Inductive wfX (kn: nat) (tn: nat) : exp -> Prop :=
 | WfX_XVar 
   :  forall ti
   ,  ti < tn
   -> wfX kn tn (XVar ti)
 
 | WfX_XLAM
   :  forall x
   ,  wfX (S kn) tn x
   -> wfX kn tn (XLAM x)

 | WfX_XAPP
   :  forall x1 t2
   ,  wfX kn tn x1 -> wfT kn t2
   -> wfX kn tn (XAPP x1 t2)

 | WfX_XLam
   :  forall t1 x2
   ,  wfT kn t1 -> wfX kn (S tn) x2
   -> wfX kn tn (XLam t1 x2)

 | WfX_XApp 
   :  forall x1 x2
   ,  wfX kn tn x1 -> wfX kn tn x2
   -> wfX kn tn (XApp x1 x2)

 | WfX_XCon
   :  forall dc ts xs
   ,  Forall (wfT kn)    ts
   -> Forall (wfX kn tn) xs
   -> wfX kn tn (XCon dc ts xs)

 | WfX_XCase
   :  forall x alts
   ,  wfX kn tn x 
   -> Forall (wfA kn tn) alts
   -> wfX kn tn (XCase x alts)

 | WfX_XPrim
   :  forall p xs
   ,  Forall (wfX kn tn) xs
   -> wfX kn tn (XPrim p xs)

 | WfX_XLit
   :  forall l
   ,  wfX kn tn (XLit l)

with    wfA (kn: nat) (tn: nat) : alt -> Prop :=
 | WfA_AAlt
   :  forall dc ds x tsArgs tResult
   ,  getDataDef dc ds = Some (DefData dc tsArgs tResult)
   -> wfX kn (tn + length tsArgs) x
   -> wfA kn tn (AAlt dc x).

Hint Constructors wfX.
Hint Constructors wfA.


(* Closed expressions are well formed under an empty environment. *)
Definition closedX (xx: exp) : Prop
 := wfX O O xx.
Hint Unfold closedX.


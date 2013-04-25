
Require Export Iron.Language.SystemF2Data.Type.
Require Export Iron.Language.SystemF2Data.Exp.Lit.
Require Export Iron.Language.SystemF2Data.Exp.Prim.


(********************************************************************)
(* Expressions *)
Inductive exp : Type :=
 (* Variables *)
 | XVar   : nat -> exp

 (* Type abstraction *)
 | XLAM   : exp -> exp
 
 (* Type application. *)
 | XAPP   : exp -> ty  -> exp

 (* Function abstraction. *)
 | XLam   : ty  -> exp -> exp

 (* Function application. *)
 | XApp   : exp -> exp -> exp

 (* Saturated data constructors. *)
 | XCon   : datacon  -> list ty  -> list exp -> exp

 (* Case expressions. *)
 | XCase  : exp      -> list alt -> exp

 (* Saturated primitive operators. *)
 | XPrim  : prim     -> list exp -> exp

 (* Primitive literals. *)
 | XLit   : lit      -> exp

 (* Alternatives *)
with alt     : Type :=
 | AAlt   : datacon -> exp -> alt.

Hint Constructors exp.
Hint Constructors alt.


(********************************************************************)
(* Mutual induction principle for expressions.
   As expressions are indirectly mutually recursive with lists,
   Coq's Combined scheme command won't make us a strong enough
   induction principle, so we need to write it out by hand. *)
Theorem exp_mutind
 : forall 
    (PX : exp -> Prop)
    (PA : alt -> Prop)
 ,  (forall n,                                PX (XVar n))
 -> (forall x1,      PX x1                 -> PX (XLAM x1))
 -> (forall x1 t2,   PX x1                 -> PX (XAPP x1 t2))
 -> (forall t  x1,   PX x1                 -> PX (XLam t x1))
 -> (forall x1 x2,   PX x1 -> PX x2        -> PX (XApp x1 x2))
 -> (forall dc ts xs,         Forall PX xs -> PX (XCon dc ts xs))
 -> (forall x  aa,   PX x  -> Forall PA aa -> PX (XCase x aa))
 -> (forall p xs,    Forall PX xs          -> PX (XPrim p xs))
 -> (forall l,                                PX (XLit  l))
 -> (forall dc x,    PX x                  -> PA (AAlt dc x))
 ->  forall x, PX x.
Proof. 
 intros PX PA.
 intros var tlam tapp lam app con case prim lit alt.
 refine (fix  IHX x : PX x := _
         with IHA a : PA a := _
         for  IHX).

 - case x; intros.
   + apply var.
   + apply tlam. apply IHX.
   + apply tapp. apply IHX.
   + apply lam.  apply IHX.
   + apply app.  apply IHX. apply IHX.
   + apply con.  induction l0; intuition.
   + apply case. apply IHX. induction l; intuition.
   + apply prim. induction l;  intuition. 
   + apply lit.

 - case a; intros.
   + apply alt.  apply IHX.
Qed.



Require Export Iron.Language.SystemF2Data.Exp.Base.
Require Export Iron.Language.SystemF2Data.Exp.Relation.WfX.


(********************************************************************)
(* Weak normal forms cannot be reduced further by 
   call-by-value evaluation. *)
Inductive wnfX : exp -> Prop :=
 | Wnf_XVar 
   : forall i
   , wnfX (XVar i)

 | Wnf_XLAM
   : forall x1
   , wnfX (XLAM x1)

 | Wnf_XLam
   : forall t1 x2
   , wnfX (XLam t1 x2)

 | Wnf_XCon
   :  forall dc ts xs
   ,  Forall wnfX xs
   -> wnfX (XCon dc ts xs)

 | Wnf_XLit
   :  forall l
   ,  wnfX (XLit l).
Hint Constructors wnfX.


(********************************************************************)
(* Values are closed expressions that cannot be reduced further. *)
Inductive value : exp -> Prop :=
 | Value 
   :  forall xx
   ,  wnfX xx -> closedX xx
   -> value xx.
Hint Constructors value.


Lemma value_wnfX 
 : forall xx, value xx -> wnfX xx.
 Proof. intros. inverts H. auto. Qed.
Hint Resolve value_wnfX.


Lemma value_closedX 
 : forall xx, value xx -> closedX xx.
 Proof. intros. inverts H. auto. Qed.
Hint Resolve value_closedX.


Lemma value_wnfXs_XCon
 : forall ts xs dc
 , value (XCon dc ts xs) -> Forall wnfX xs.
Proof.
 intros. inverts H. inverts H0. auto.
Qed.
Hint Resolve value_wnfXs_XCon.


Lemma value_closedXs_XCon
 : forall ts xs dc
 , value (XCon dc ts xs) -> Forall closedX xs.
Proof.
 intros. inverts H. inverts H1. auto.
Qed.
Hint Resolve value_closedXs_XCon.


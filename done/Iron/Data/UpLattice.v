

Inductive Bag (a : Type) : Type  :=
 | BagNone : Bag a
 | BagOne  : a -> Bag a
 | BagJoin : Bag a -> Bag a -> Bag a.


(* Equivalence of Bags *)
Inductive BagEquiv {A} : Bag A -> Bag A -> Prop :=
 | BagEquivRefl
   :  forall (b : Bag A)
   ,  BagEquiv b b

 | BagEquivSym
   :  forall (b1 b2 : Bag A)
   ,  BagEquiv b1 b2
   -> BagEquiv b2 b1

 | BagEquivTrans
   :  forall (b1 b2 b3 : Bag A)
   ,  BagEquiv b1 b2 -> BagEquiv b2 b3
   -> BagEquiv b1 b3

 | BagEquivJoinComm
   :  forall (b1 b2 : Bag A)
   ,  BagEquiv (BagJoin A b1 b2) (BagJoin A b2 b1)

 | BagEquivJoinIdemp
   :  forall (b : Bag A)
   ,  BagEquiv b (BagJoin A b b)

 | BagEquivJoinNone
   :  forall (b : Bag A)
   ,  BagEquiv (BagJoin A b (BagNone A)) b.

Hint Constructors BagEquiv.


(* Subsumption of bags *)
Inductive BagSubs {A} : Bag A -> Bag A -> Prop :=
 | BagSubsRefl
   : forall (b : Bag A)
   , BagSubs b b

 | BagSubsTrans
   :  forall (b1 b2 b3 : Bag A)
   ,  BagSubs b1 b2 -> BagSubs b2 b3
   -> BagSubs b1 b3

 | BagSubsNone
   : forall (b : Bag A)
   , BagSubs b (BagNone A).




Require Export Iron.SystemF2Effect.Type.Exp.Base.


(* Equivalence for sum types *)
Inductive EquivT : ty -> ty -> Prop :=
 | EqRefl 
   : forall t
   , EquivT t t

 | EqSumSym
   : forall t1 t2
   , EquivT (TSum t1 t2) (TSum t2 t1)

 | EqSumIdemp
   : forall t1
   , EquivT t1 (TSum t1 t1)

 | EqSumBot
   : forall t1 k
   , EquivT t1 (TSum t1 (TBot k)).

Hint Constructors EquivT.

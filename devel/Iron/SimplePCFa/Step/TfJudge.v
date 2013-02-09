
Require Import Iron.SimplePCFa.Step.Frame.
Require Import Iron.SimplePCFa.Step.Prim.
Require Import Iron.SimplePCFa.Value.


(* Type of a frame stack.
   The frame stack is like a continuation that takes an expression of a certain
   type and produces a new expression. *)
Inductive TYPEF : tyenv -> stack -> ty -> ty -> Prop := 
 | TfNil 
   :  forall te t
   ,  TYPEF  te nil t t

 | TfCons
   :  forall te fs t1 t2 t3 x2
   ,  TYPEX (te :> t1) x2 t2
   -> TYPEF  te fs t2 t3
   -> TYPEF  te (fs :> FLet t1 x2) t1 t3.
Hint Constructors TYPEF.


(* Type of an expression in a frame context. *)
Inductive TYPEC : tyenv -> stack -> exp -> ty -> Prop :=
 | TcExp
   :  forall te fs x t1 t2
   ,  TYPEF te fs t1 t2
   -> TYPEX te x  t1
   -> TYPEC te fs x t2.
Hint Constructors TYPEC.



Require Export Iron.Language.SystemF2Effect.Value.TyJudge.
Require Export Iron.Language.SystemF2Effect.Step.Frame.


(* Store properties model use frames on stack. *)
Definition STOREP (fs : stack) (sp : stprops)
 := forall n, In (FUse n) fs <-> In (SRegion n) sp.


(* Type of a frame stack.
   The frame stack is like a continuation that takes an expression of a certain
   type and produces a new expression. *)
Inductive TYPEF : kienv -> tyenv -> stenv -> stack -> ty -> ty -> ty -> Prop := 
 | TfNil 
   :  forall ke te se t
   ,  TYPEF  ke te se nil t t (TBot KEffect)

 | TfConsLet
   :  forall ke te se fs sp t1 x2 t2 e2 t3 e3
   ,  STOREP fs sp
   -> TYPEX  ke (te :> t1) se sp                 x2 t2 e2
   -> TYPEF  ke te         se fs                 t2 t3 e3
   -> TYPEF  ke te         se (fs :> FLet t1 x2) t1 t3 (TSum e2 e3)

 | TfConsUse
   :  forall ke te se fs t1 t2 e2 n
   ,  not (In (FUse n) fs)
   -> TYPEF  ke te se  fs                t1 t2 e2
   -> TYPEF  ke te se (fs :> FUse n)     t1 t2 e2.

Hint Constructors TYPEF.


(* Type of an expression in a frame context. *)
Inductive TYPEC : kienv -> tyenv -> stenv -> stack -> exp -> ty -> ty -> Prop :=
 | TcExp
   :  forall ke te se sp fs x1 t1 e1 t2 e2
   ,  STOREP fs sp
   -> TYPEX  ke te se sp x1 t1 e1
   -> TYPEF  ke te se fs t1 t2 e2
   -> TYPEC  ke te se fs x1 t2 (TSum e1 e2).
Hint Constructors TYPEC.
(* TODO: going to need to mask effects involving region handles from e1 *)



  
   


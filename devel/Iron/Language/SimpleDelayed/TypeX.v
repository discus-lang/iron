
Require Export Iron.Language.SimpleDelayed.Exp.
Require Export Iron.Language.SimpleDelayed.Ty.


Fixpoint stripB (b: bind): sig :=
 match b with
 | BBind n t _ => SSig n t
 end.


(* Typing judgement assigns a type to an expression. *)
Inductive 
 TypeX : tyenv -> exp -> ty -> Prop :=
 | TxVar 
   :  forall te n t
   ,  lookupEnv n te = Some t
   -> TypeX te (XVar n) t

 | TxLam
   :  forall te bs n1 t1 x2 t2
   ,  Forall (TypeB te) bs
   -> TypeX (te >< map stripB bs :> SSig n1 t1) x2 t2
   -> TypeX te (XLam bs n1 t1 x2) (TFun t1 t2)

 | TxApp
   :  forall te x1 x2 t1 t2
   ,  TypeX te x1 (TFun t1 t2)
   -> TypeX te x2 t1
   -> TypeX te (XApp x1 x2) t2

 with TypeB : tyenv -> bind -> Prop :=
 | TsSig
   :  forall te n t x
   ,  TypeX te x t
   -> TypeB te (BBind n t x).

Hint Constructors TypeX.
Hint Constructors TypeB.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_type :=
 repeat 
  (match goal with 
   | [ H: TypeX _ (XVar _) _       |- _ ] => inverts H
   | [ H: TypeX _ (XLam _ _ _ _) _ |- _ ] => inverts H
   | [ H: TypeX _ (XApp _ _) _     |- _ ] => inverts H
   end).


Definition Closed (xx: exp) : Prop := 
 exists t, TypeX nil xx t.



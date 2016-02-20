
Require Export Iron.Language.DelayedSystemF.Exp.
Require Export Iron.Language.DelayedSystemF.SubstTT.


(*******************************************************************)
(* Typing judgement assigns a type to an expression. *)
Inductive TypeX : kienv -> tyenv -> exp -> ty -> Prop :=
 | TxVar 
   :  forall ke te v t
   ,  lookupEnv v te = Some t
   -> TypeX  ke te (XVar v) t

 | TxAbs
   :  forall ke te sx v1 t1 x2 t2
   ,  ForallSubstXT (TypeX ke te) sx
   -> TypeX  ke (te >< stripS sx :> SSig v1 t1) x2 t2
   -> TypeX  ke te (XAbs sx v1 t1 x2) (TFun t1 t2)

 (* TODO need type equiv here, rather than just t1 *)
 | TxApp
   :  forall ke te x1 x2 t1 t2
   ,  TypeX  ke te x1 (TFun t1 t2)
   -> TypeX  ke te x2 t1
   -> TypeX  ke te (XApp x1 x2) t2

 | TxABS
   :  forall ke te st sx a1 k1 x2 t2
   ,  TypeX  (ke >< stripS st :> SSig a1 k1) (te >< stripS sx) x2 t2
   -> TypeX  ke te (XABS st sx a1 k1 x2) (TForall st a1 k1 t2)

 | TxAPP
   :  forall ke te st a1 k1 t1 x1 t2
   ,  TypeX  ke te x1 (TForall st a1 k1 t1)
   -> TypeX  ke te (XAPP x1 t2) (substTT (st :> BBind a1 k1 t2) t1).

Hint Constructors TypeX.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_type :=
 repeat 
  (match goal with 
   | [ H: TypeX _ _ (XVar _) _         |- _ ] => inverts H
   | [ H: TypeX _ _ (XAbs _ _ _ _) _   |- _ ] => inverts H
   | [ H: TypeX _ _ (XApp _ _) _       |- _ ] => inverts H
   | [ H: TypeX _ _ (XABS _ _ _ _ _) _ |- _ ] => inverts H
   | [ H: TypeX _ _ (XAPP _ _) _       |- _ ] => inverts H
   end).


(* Closed expressions are well typed under an empty environment. *)
Definition Closed (xx: exp) : Prop := 
 exists t, TypeX nil nil xx t.


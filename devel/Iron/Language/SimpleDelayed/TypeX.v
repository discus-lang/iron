
Require Export Iron.Language.SimpleDelayed.Exp.


Fixpoint stripB (b: bind): sig :=
 match b with
 | BBind n t _ => SSig n t
 end.


(* Typing judgement assigns a type to an expression. *)
Inductive TypeX : tyenv -> exp -> ty -> Prop :=
 | TxVar 
   :  forall te n t
   ,  lookupEnv n te = Some t
   -> TypeX te (XVar n) t

 | TxLam
   :  forall te bs n1 t1 x2 t2
   ,  Forall (TypeB te) bs
   -> TypeX (te >< map stripB bs :> SSig n1 t1) x2 t2
   -> TypeX te (XAbs bs n1 t1 x2) (TFun t1 t2)

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
   | [ H: TypeX _ (XAbs _ _ _ _) _ |- _ ] => inverts H
   | [ H: TypeX _ (XApp _ _) _     |- _ ] => inverts H
   | [ H: TypeB _ (BBind _ _ _)    |- _ ] => inverts H
   end).


(* Closed expressions are well typed under an empty environment. *)
Definition Closed (xx: exp) : Prop := 
 exists t, TypeX nil xx t.



(*******************************************************************)
(* Forms of terms lemma. *)
Lemma done_lam 
 :  forall x t1 t2
 ,  TypeX nil x (TFun t1 t2)
 -> Done x
 -> isXAbs x.
Proof.
 intros. gen t1 t2.
 induction x; intros.

 - Case "XVar".
   nope.

 - Case "XLam".
   nope.

 - Case "XApp".
   inverts H0.
   + nope.

   + destruct x1.
     * nope.

     * rip.
       assert (Value (XAbs l n t x1)); auto.
       nope.

     * inverts_type.
       rip.
       assert (isXAbs (XApp x1_1 x1_2)).
        eapply IHx1. eauto. nope.
Qed.



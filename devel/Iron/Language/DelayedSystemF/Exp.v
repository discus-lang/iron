
Require Export Iron.Language.DelayedSystemF.Base.
Require Export Iron.Language.DelayedSystemF.Ty.


(********************************************************************)
(* Value Expressions *)
Inductive exp : Type :=
 (* Variables want to be named. *)
 | XVar  (v: name) : exp

 (* Function abstraction. *)
 | XAbs  (st: @subst ty ki) (sx: @subst exp ty) 
         (v: name) (t: ty)  (x: exp) : exp

 (* Function application. *)
 | XApp  (x1: exp) (x2: exp) : exp

 (* Type abstraction. *)
 | XABS  (st: @subst ty ki) (sx: @subst exp ty)
         (a: name) (k: ki)  (x: exp) : exp

 (* Type application. *)
 | XAPP  (x1: exp) (t2: ty) : exp.

Hint Constructors exp.


(* Indirect induction principle for expressions.

   In the definition of 'exp', abstractions contain a list of 
   subexpressions, so 'exp' is indirectly defined via the list 
   data type.

   In the following induction principle, when proving a property
   of abstractions we know the property being proved applies to 
   subexpressions contained in those lists. The automatically
   generated induction principle 'exp_ind' doesn't give us this.
*)
Theorem exp_iind
 : forall
    (PX : exp -> Prop)

 ,  (  forall n
    ,  PX (XVar n))

 -> (  forall st sx n t x
    ,  Forall (fun b => PX (expOfBind b)) sx
    -> PX x
    -> PX (XAbs st sx n t x))

 -> (  forall x1 x2
    ,  PX x1  -> PX x2
    -> PX (XApp x1 x2))

 -> (  forall st sx a k x
    ,  Forall (fun b => PX (expOfBind b)) sx
    -> PX x
    -> PX (XABS st sx a k x))

 -> (  forall x1 t2
    ,  PX x1
    -> PX (XAPP x1 t2))

 -> forall  x, PX x.
Proof.
 intros PX.
 intros Hvar Habs Happ HABS HAPP.
 refine (fix IHX x: PX x := _).

 case x; intros.
 - apply Hvar.

 - eapply Habs.
   induction sx as [| b].
   + apply Forall_nil.
   + apply Forall_cons.
     * destruct b. simpl. eapply IHX.
     * assumption.
   + apply IHX.

 - apply Happ.
   + apply IHX.
   + apply IHX.

 - apply HABS.
   induction sx as [|b].
   + apply Forall_nil.
   + apply Forall_cons.
     * destruct b. simpl. eapply IHX.
     * assumption.
   + apply IHX.

 - apply HAPP.
   + apply IHX.
Qed.


(********************************************************************)
(* Values *)
Inductive Value : exp -> Prop :=
 | ValueAbs 
   :  forall st sx v t x
   ,  Value (XAbs st sx v t x)

 | ValueABS
   :  forall st sx a k x
   ,  Value (XABS st sx a k x).

Hint Constructors Value.


Lemma isValue_not_var
 : forall v
 , ~Value (XVar v).
Proof.
 intros. intuition. inverts H.
Qed.
Hint Resolve isValue_not_var.


Lemma isValue_not_app
 : forall x1 x2
 , ~Value (XApp x1 x2).
Proof.
 intros. intuition. inverts H.
Qed.
Hint Resolve isValue_not_app.


Lemma isValue_not_APP
 : forall x1 t2
 , ~Value (XAPP x1 t2).
Proof.
 intros. intuition. inverts H.
Qed.
Hint Resolve isValue_not_APP.


(* Done expressions have finished evaluating. *)
Inductive Done  : exp -> Prop :=
 | DoneVar 
   :  forall v
   ,  Done (XVar v)

 | DoneValue
   :  forall x
   ,  Value  x
   -> Done   x

 | DoneApp 
   :  forall x1 x2
   ,  Done x1 /\ ~Value x1
   -> Done (XApp x1 x2)

 | DoneAPP 
   :  forall x1 t2
   ,  Done x1 /\ ~Value x1
   -> Done (XAPP x1 t2).

Hint Constructors Done.


(* Invert all hypothesis that are compound done statements. *)
Ltac inverts_done :=
 repeat 
  (match goal with 
   | [ H: Done (XApp _ _) |- _ ] => inverts H
   | [ H: Done (XAPP _ _) |- _ ] => inverts H
   end).


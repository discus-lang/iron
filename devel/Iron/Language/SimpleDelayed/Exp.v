
Require Export Iron.Language.SimpleDelayed.Base.
Require Export Iron.Language.SimpleDelayed.Ty.



(* Value Expressions *)
Inductive exp : Type :=
 (* a named variable. *)
 | XVar    : nat       -> exp

 (* function abstraction *)
 | XAbs    : list bind -> nat -> ty  -> exp -> exp   

 (* function application *)
 | XApp    : exp       -> exp -> exp

with bind  : Type := 
 (* binding in a substitution. *)
 | BBind   : nat -> ty -> exp -> bind.

Hint Constructors exp.
Hint Constructors bind.


(* Expression substitutions. *)
Definition substx := list bind.


(********************************************************************)
(* Mutual induction principle for expressions. *)
Theorem exp_mutind
 : forall
    (PX  : exp        -> Prop)
    (PB  : bind       -> Prop)
 ,  (forall n,                                  PX (XVar n))
 -> (forall bs n t x, Forall PB bs -> PX x   -> PX (XAbs bs n t x))
 -> (forall x1 x2,    PX x1  -> PX x2        -> PX (XApp x1 x2))
 -> (forall n t x,    PX x                   -> PB (BBind  n t x))
 -> forall x, PX x.
Proof.
 intros PX PB.
 intros var abs app bind.
 refine (fix   IHX x : PX x := _  
         with  IHB b : PB b := _ 
         for  IHX).

 - Case "expressions".
   case x; intros.
   + apply var.
   + apply abs. induction l; intuition. apply IHX.
   + apply app. apply IHX. apply IHX.

 - Case "bindings".
   case b; intros.
   + apply bind. apply IHX.
Qed.


(********************************************************************)
(* Predicates. *)
Definition isXAbs (x1: exp): Prop := 
 (exists bs n t x, x1 = XAbs bs n t x).


Lemma isXAbs_true
 : forall bs n t x, isXAbs (XAbs bs n t x).
Proof.
 intros.
 unfold isXAbs.
 exists bs. exists n. exists t. exists x.
 trivial.
Qed.
Hint Resolve isXAbs_true.


Lemma isXAbs_XVar
 : forall n
 , ~isXAbs (XVar n).
Proof.
 intuition. nope.
Qed.
Hint Resolve isXAbs_XVar.


Lemma isXAbs_XApp
 : forall x1 x2
 , ~isXAbs (XApp x1 x2).
Proof.
 intuition. nope.
Qed.
Hint Resolve isXAbs_XApp.


(********************************************************************)
(* Values *)
Inductive Value : exp -> Prop :=
 | ValueAbs 
   :  forall bs v t x
   ,  Value (XAbs bs v t x).

Hint Constructors Value.


Lemma isValue_not_var
 : forall n
 , ~Value (XVar n).
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


(* Done expressions have finished evaluating. *)
Inductive Done  : exp -> Prop :=
 | DoneVar 
   :  forall n
   ,  Done (XVar n)

 | DoneValue
   :  forall x
   ,  Value  x
   -> Done   x

 | DoneApp 
   :  forall x1 x2
   ,  Done x1 /\ ~Value x1
   -> Done (XApp x1 x2).

Hint Constructors Done.


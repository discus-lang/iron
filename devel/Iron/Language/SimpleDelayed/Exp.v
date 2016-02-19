
Require Export Iron.Language.SimpleDelayed.Base.
Require Export Iron.Language.SimpleDelayed.Ty.


(* Value Expressions *)
Inductive exp : Type :=
 | XVar    : nat       -> exp                        (* named variable. *)
 | XLam    : list bind -> nat -> ty  -> exp -> exp   (* function abstraction *)
 | XApp    : exp       -> exp -> exp                 (* function application *)

with bind  : Type := 
 | BBind   : nat -> ty -> exp -> bind.

Hint Constructors exp.
Hint Constructors bind.


(* Expression substitutions. *)
Definition substx := list bind.


(* Mutual induction principle for expressions. *)
Theorem exp_mutind
 : forall
    (PX  : exp        -> Prop)
    (PB  : bind       -> Prop)
 ,  (forall n,                                  PX (XVar n))
 -> (forall bs n t x, Forall PB bs -> PX x   -> PX (XLam bs n t x))
 -> (forall x1 x2,    PX x1  -> PX x2        -> PX (XApp x1 x2))
 -> (forall n t x,    PX x                   -> PB (BBind  n t x))
 -> forall x, PX x.
Proof.
 intros PX PB.
 intros var lam app bind.
 refine (fix   IHX x : PX x := _  
         with  IHB b : PB b := _ 
         for  IHX).

 - Case "expressions".
   case x; intros.
   + apply var.
   + apply lam. induction l; intuition. apply IHX.
   + apply app. apply IHX. apply IHX.

 - Case "bindings".
   case b; intros.
   + apply bind. apply IHX.
Qed.


Definition isXLam (x1: exp): Prop := 
 (exists bs n t x, x1 = XLam bs n t x).


Lemma isXLam_true
 : forall bs n t x, isXLam (XLam bs n t x).
Proof.
 intros.
 unfold isXLam.
 exists bs. exists n. exists t. exists x.
 trivial.
Qed.
Hint Resolve isXLam_true.


Lemma isXLam_XVar
 : forall n
 , ~isXLam (XVar n).
Proof. 
 intros. intuition. nope.
Qed.
Hint Resolve isXLam_XVar.


Lemma isXLam_XApp
 : forall x1 x2
 , ~isXLam (XApp x1 x2).
Proof.
 intros. intuition. nope.
Qed.
Hint Resolve isXLam_XApp.



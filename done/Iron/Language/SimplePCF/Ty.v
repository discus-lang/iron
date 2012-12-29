
Require Export Iron.Language.SimplePCF.Exp.

(* Typing judgement assigns a type to an expression. *)
Inductive TYPE : tyenv -> exp -> ty -> Prop :=
 (* Variables *)
 | TyVar 
   :  forall te i t
   ,  get i te = Some t
   -> TYPE te (XVar i) t

 (* Function abstraction *)
 | TyLam
   :  forall te x t1 t2
   ,  TYPE (te :> t1) x t2
   -> TYPE te (XLam t1 x) (TFun t1 t2)

 (* Function application *)
 | TyApp
   :  forall te x1 x2 t1 t2
   ,  TYPE te x1 (TFun t1 t2)
   -> TYPE te x2 t1
   -> TYPE te (XApp x1 x2) t2

  (* Fixpoints *)
  | TyFix
    :  forall te x1 t1
    ,  TYPE (te :> t1) x1          t1
    -> TYPE te        (XFix t1 x1) t1

  (* Naturals ************************)
  | TyNat
    :  forall te n
    ,  TYPE te (XNat n) tNat

  (* Take the successor of a natural *)
  | TySucc
    :  forall te x1
    ,  TYPE te x1 tNat
    -> TYPE te (XSucc x1) tNat

  (* Take the predecessor of a natural *)
  | TyPred
    :  forall te x1
    ,  TYPE te x1 tNat
    -> TYPE te (XPred x1) tNat

  (* Booleans *************************)
  | TyTrue
    :  forall te 
    ,  TYPE te XTrue tBool
 
  | TyFalse
    :  forall te
    ,  TYPE te XFalse tBool
 
  | TyIsZero
    :  forall te x1
    ,  TYPE te x1 tNat
    -> TYPE te (XIsZero x1) tBool

  (* Branching ************************)
  | TyIf
    :  forall te x1 x2 x3 tR
    ,  TYPE te x1 tBool
    -> TYPE te x2 tR -> TYPE te x3 tR
    -> TYPE te (XIf x1 x2 x3) tR.

Hint Constructors TYPE.


(*******************************************************************)
(* Forms of values. 
   If we know the type of a value then we know the
   form of that value. *)

Lemma value_lam 
 :  forall xx te t1 t2
 ,  value xx 
 -> TYPE te xx (TFun t1 t2)
 -> (exists t x, xx = XLam t x).
Proof. destruct xx; burn. Qed.
Hint Resolve value_lam.

Lemma value_nat
 :  forall te x
 ,  value x
 -> TYPE te x tNat
 -> (exists n, x = XNat n).
Proof. destruct x; burn. Qed.
Hint Resolve value_nat.

Lemma value_bool
 :  forall te x
 ,  value x
 -> TYPE te x tBool
 -> x = XFalse \/ x = XTrue.
Proof. destruct x; burn. Qed.
Hint Resolve value_bool.


(********************************************************************)
(* A well typed expression is well formed *)
Theorem type_wfX
 :  forall te x t
 ,  TYPE te x t
 -> wfX  te x.
Proof.
 intros te x t HT. gen te t.
 induction x; rip; inverts HT; burn.
Qed.
Hint Resolve type_wfX.


(* Weakening the type environment in typine judgements.
   We can insert a new type into the type environment, provided we
   lift existing references to types higher in the stack across
   the new one. *)
Lemma type_tyenv_insert
 :  forall te ix x t1 t2
 ,  TYPE te x t1
 -> TYPE (insert ix t2 te) (liftX ix x) t1.
Proof.
 intros te ix x t1 t2 HT. gen ix te t1.
 induction x; rip; inverts HT; burn.

 Case "XVar".
  simpl; lift_cases; burn.

 Case "XLam".
  simpl.
  apply TyLam.
  rewrite insert_rewind. 
  apply IHx; burn.

 Case "XFix".
  simpl.
  apply TyFix.
  rewrite insert_rewind.
  apply IHx; burn.
Qed.


Lemma type_tyenv_weaken
 :  forall te x t1 t2
 ,  TYPE  te        x           t1
 -> TYPE (te :> t2) (liftX 0 x) t1.
Proof.
 intros.
 rrwrite (te :> t2 = insert 0 t2 te).
 burn using type_tyenv_insert.
Qed.


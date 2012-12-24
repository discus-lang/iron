
Require Export Iron.Language.SimplePCF.Exp.

(* Typing judgement assigns a type to an expression. *)
Inductive TYPE : tyenv -> exp -> ty -> Prop :=
 (* Variables *)
 | TYVar 
   :  forall te i t
   ,  get i te = Some t
   -> TYPE te (XVar i) t

 (* Function abstraction *)
 | TYLam
   :  forall te x t1 t2
   ,  TYPE (te :> t1) x t2
   -> TYPE te (XLam t1 x) (TFun t1 t2)

 (* Function application *)
 | TYApp
   :  forall te x1 x2 t1 t2
   ,  TYPE te x1 (TFun t1 t2)
   -> TYPE te x2 t1
   -> TYPE te (XApp x1 x2) t2

  (* Fixpoints *)
  | TYFix
    :  forall te x1 t1
    ,  TYPE (te :> t1) x1          t1
    -> TYPE te        (XFix t1 x1) t1

  (* Naturals ************************)
  | TYNat
    :  forall te n
    ,  TYPE te (XNat n) tNat

  (* Take the successor of a natural *)
  | TYSucc
    :  forall te x1
    ,  TYPE te x1 tNat
    -> TYPE te (XSucc x1) tNat

  (* Take the predecessor of a natural *)
  | TYPred
    :  forall te x1
    ,  TYPE te x1 tNat
    -> TYPE te (XPred x1) tNat

  (* Booleans *************************)
  | TYTrue
    :  forall te 
    ,  TYPE te XTrue tBool
 
  | TYFalse
    :  forall te
    ,  TYPE te XFalse tBool
 
  | TYIsZero
    :  forall te x1
    ,  TYPE te x1 tNat
    -> TYPE te (XIsZero x1) tBool

  (* Branching ************************)
  | TYIf
    :  forall te x1 x2 x3 tR
    ,  TYPE te x1 tBool
    -> TYPE te x2 tR -> TYPE te x3 tR
    -> TYPE te (XIf x1 x2 x3) tR.

Hint Constructors TYPE.


(********************************************************************)
(* A well typed expression is well formed *)
Theorem type_wfX
 :  forall te x t
 ,  TYPE te x t
 -> wfX  te x.
Proof.
 intros. gen te t.
 induction x; intros; inverts H; simpl; eauto 10.
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
 intros. gen ix te t1.
 induction x; intros; simpl; inverts H; eauto.

 Case "XVar".
  lift_cases; intros; auto.

 Case "XLam".
  apply TYLam.
  rewrite insert_rewind. 
   apply IHx. auto.

 Case "XFix".
  apply TYFix.
  rewrite insert_rewind.
   apply IHx. auto.
Qed.


Lemma type_tyenv_weaken
 :  forall te x t1 t2
 ,  TYPE  te        x           t1
 -> TYPE (te :> t2) (liftX 0 x) t1.
Proof.
 intros.
 assert (te :> t2 = insert 0 t2 te).
  simpl. destruct te; auto.
  rewrite H0. apply type_tyenv_insert. auto.
Qed.



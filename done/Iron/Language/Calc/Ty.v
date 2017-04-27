
Require Export Iron.Language.Calc.Exp.

Inductive TYPE : exp -> ty -> Prop :=
 | TyNum    :  forall n
            ,  TYPE (XNum n)    TNum

 | TyBool   :  forall b
            ,  TYPE (XBool b)   TBool

 | TyString :  forall s
            ,  TYPE (XString s) TString

 | TyAdd    :  forall e1 e2
            ,  TYPE e1 TNum -> TYPE e2 TNum
            -> TYPE (XAdd e1 e2) TNum

 | TyMul    :  forall e1 e2
            ,  TYPE e1 TNum -> TYPE e2 TNum
            -> TYPE (XMul e1 e2) TNum

 | TyLess   :  forall e1 e2
            ,  TYPE e1 TNum -> TYPE e2 TNum
            -> TYPE (XLess e1 e2) TBool

 | TyMore   :  forall e1 e2
            ,  TYPE e1 TNum -> TYPE e2 TNum
            -> TYPE (XMore e1 e2) TBool

 | TyAnd    :  forall e1 e2
            ,  TYPE e1 TBool -> TYPE e2 TBool
            -> TYPE (XAnd e1 e2) TBool

 | TyOr     :  forall e1 e2
            ,  TYPE e1 TBool -> TYPE e2 TBool
            -> TYPE (XOr e1 e2) TBool

 | TyIf     :  forall e1 e2 e3 t
            ,  TYPE e1 TBool -> TYPE e2 t -> TYPE e3 t
            -> TYPE (XIf e1 e2 e3) t.

Hint Constructors TYPE.


Lemma ValueNum 
 : forall e
 , TYPE e TNum -> VALUE e -> exists n, e = XNum n.
Proof.
 intros.
 destruct e; nope.
 exists n. auto.
Qed.
Hint Resolve ValueNum.


Lemma ValueBool 
 : forall e
 , TYPE e TBool -> VALUE e -> exists b, e = XBool b.
Proof.
 intros.
 destruct e; nope.
 exists b. auto.
Qed.
Hint Resolve ValueBool.


Lemma ValueString 
 : forall e
 , TYPE e TString -> VALUE e -> exists s, e = XString s.
Proof.
 intros.
 destruct e; nope.
 exists s. auto.
Qed.
Hint Resolve ValueString.



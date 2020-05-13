
Require Export Iron.Language.Calc.Exp.
Require Export Iron.Hectic.Nope.

Inductive TYPE : tm -> ty -> Prop :=
 | TyNat    :  forall n
            ,  TYPE (MNat n)    TNat

 | TyBool   :  forall b
            ,  TYPE (MBool b)   TBool

 | TyText   :  forall s
            ,  TYPE (MText s)   TText

 | TyAdd    :  forall e1 e2
            ,  TYPE e1 TNat -> TYPE e2 TNat
            -> TYPE (MAdd e1 e2) TNat

 | TyLess   :  forall e1 e2
            ,  TYPE e1 TNat -> TYPE e2 TNat
            -> TYPE (MLess e1 e2) TBool

 | TyAnd    :  forall e1 e2
            ,  TYPE e1 TBool -> TYPE e2 TBool
            -> TYPE (MAnd e1 e2) TBool

 | TyIf     :  forall e1 e2 e3 t
            ,  TYPE e1 TBool -> TYPE e2 t -> TYPE e3 t
            -> TYPE (MIf e1 e2 e3) t.
Hint Constructors TYPE : calc.


Lemma canonical_value_nat
 :  forall v
 ,  TYPE (MVal v) TNat
 -> exists n, v = VNat n.
Proof.
 intros.
 destruct v; try nope.
 - exists n; auto.
Qed.
Hint Resolve canonical_value_nat : calc.


Lemma canonical_value_bool
 :  forall v
 ,  TYPE (MVal v) TBool
 -> exists b, v = VBool b.
Proof.
 intros.
 destruct v; try nope.
 - exists b; auto.
Qed.
Hint Resolve canonical_value_bool : calc.


Lemma canonical_value_text
 :  forall v
 ,  TYPE (MVal v) TText
 -> exists t, v = VText t.
Proof.
 intros.
 destruct v; try nope.
 - exists s; auto.
Qed.
Hint Resolve canonical_value_text : calc.


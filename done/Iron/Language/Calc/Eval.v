
Require Export Iron.Language.Calc.Exp.


Inductive EVAL : tm -> va -> Prop :=
 | EvVal    :  forall v
            ,  EVAL (MVal v)      v

 | EvAdd    :  forall m1 m2 n1 n2
            ,  EVAL m1 (VNat n1) -> EVAL m2 (VNat n2)
            -> EVAL (MAdd m1 m2)   (VNat (n1 + n2))

 | EvLess   :  forall m1 m2 n1 n2
            ,  EVAL m1 (VNat n1) -> EVAL m2 (VNat n2)
            -> EVAL (MLess m1 m2)  (VBool (blt_nat n1 n2))

 | EvAnd    :  forall m1 m2 b1 b2
            ,  EVAL m1 (VBool b1) -> EVAL m2 (VBool b2)
            -> EVAL (MAnd m1 m2)   (VBool (andb b1 b2))

 | IfTrue   :  forall m1 m2 m3 v2
            ,  EVAL m1 (VBool true)
            -> EVAL m2 v2
            -> EVAL (MIf m1 m2 m3) v2

 | IfFalse  :  forall m1 m2 m3 v3
            ,  EVAL m1 (VBool false)
            -> EVAL m3 v3
            -> EVAL (MIf m1 m2 m3) v3.

Hint Constructors EVAL : core.


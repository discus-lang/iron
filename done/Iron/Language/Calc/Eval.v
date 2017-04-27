
Require Export Iron.Language.Calc.Exp.


Inductive EVAL : exp -> exp -> Prop :=
 | EvNum    :  forall n
            ,  EVAL (XNum n)    (XNum n)

 | EvBool   :  forall b
            ,  EVAL (XBool b)   (XBool b)

 | EvString :  forall s
            ,  EVAL (XString s) (XString s)

 | EvAdd    :  forall e1 e2 n1 n2
            ,  EVAL e1 (XNum n1) -> EVAL e2 (XNum n2)
            -> EVAL (XAdd e1 e2)   (XNum (n1 + n2))

 | EvMul    :  forall e1 e2 n1 n2
            ,  EVAL e1 (XNum n1) -> EVAL e2 (XNum n2)
            -> EVAL (XMul e1 e2)   (XNum (n1 * n2))

 | EvLess   :  forall e1 e2 n1 n2
            ,  EVAL e1 (XNum n1) -> EVAL e2 (XNum n2)
            -> EVAL (XLess e1 e2)  (XBool (blt_nat n1 n2))

 | EvMore   :  forall e1 e2 n1 n2
            ,  EVAL e1 (XNum n1) -> EVAL e2 (XNum n2)
            -> EVAL (XMore e1 e2)  (XBool (bgt_nat n1 n2))

 | EvAnd    :  forall e1 e2 b1 b2
            ,  EVAL e1 (XBool b1) -> EVAL e2 (XBool b2)
            -> EVAL (XAnd e1 e2)   (XBool (andb b1 b2))

 | EvOr     :  forall e1 e2 b1 b2
            ,  EVAL (XOr  e1 e2)   (XBool (orb  b1 b2))

 | IfTrue   :  forall e1 e2 e3 v2
            ,  EVAL e1 (XBool true)  -> EVAL e2 v2
            -> EVAL (XIf e1 e2 e3) v2

 | IfFalse  :  forall e1 e2 e3 v3
            ,  EVAL e1 (XBool false) -> EVAL e3 v3
            -> EVAL (XIf e1 e2 e3) v3.

Hint Constructors EVAL.


Lemma EvalValue 
 : forall e v
 , EVAL e v -> VALUE v.
Proof.
 intros. induction H; auto.
Qed.
Hint Resolve EvalValue.

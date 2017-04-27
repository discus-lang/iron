
Require Export Iron.Language.Calc.Base.


(* Types *)
Inductive ty  : Type :=
 | TNum    : ty                         (* number   type constructor *)
 | TBool   : ty                         (* boolean  type constructor *)
 | TString : ty                         (* string   type constructor *)
 | TFun    : ty  -> ty -> ty.           (* function type constructor *)
Hint Constructors ty.


(* Term Expressions *)
Inductive exp : Type :=
 | XNum    : nat    -> exp              (* number  value  *)
 | XBool   : bool   -> exp              (* boolean value  *)
 | XString : string -> exp              (* string  value  *)
 | XAdd    : exp -> exp -> exp          (* addition       *)
 | XMul    : exp -> exp -> exp          (* multiplication *)
 | XLess   : exp -> exp -> exp          (* less-than      *)
 | XMore   : exp -> exp -> exp          (* more-than      *)
 | XAnd    : exp -> exp -> exp          (* boolean and    *)
 | XOr     : exp -> exp -> exp          (* boolean or     *)
 | XIf     : exp -> exp -> exp -> exp.  (* if-then-else   *)
Hint Constructors exp.


(* Values *)
Inductive VALUE : exp -> Prop
 := VaNum    : forall n, VALUE (XNum    n)
 |  VaBool   : forall b, VALUE (XBool   b)
 |  VaString : forall s, VALUE (XString s).
Hint Constructors VALUE.

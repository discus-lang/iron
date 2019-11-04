
Require Export Iron.Language.Calc.Base.


(* Type expression *)
Inductive ty  : Type :=
 | TNat     : ty                        (* number   type constructor *)
 | TBool    : ty                        (* boolean  type constructor *)
 | TText    : ty                        (* test     type constructor *)
 | TFun     : ty  -> ty -> ty.          (* function type constructor *)
Hint Constructors ty : calc.


(* Term expression *)
Inductive va : Type :=
 | VNat     : nat    -> va              (* natural number value *)
 | VBool    : bool   -> va              (* boolean value *)
 | VText    : string -> va.             (* text value *)
Hint Constructors va : calc.

Inductive tm : Type :=
 | MVal     : va -> tm                  (* value *)
 | MAdd     : tm -> tm -> tm            (* addition       *)
 | MLess    : tm -> tm -> tm            (* less-than      *)
 | MAnd     : tm -> tm -> tm            (* boolean and    *)
 | MIf      : tm -> tm -> tm -> tm.     (* if-then-else   *)
Hint Constructors tm : calc.

Definition MNat  (n: nat)    := MVal (VNat  n).
Definition MBool (b: bool)   := MVal (VBool b).
Definition MText (t: string) := MVal (VText t).

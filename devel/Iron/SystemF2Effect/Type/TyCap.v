
Require Export Iron.SystemF2Effect.Kind.


(* Type level capabilities *)
Inductive tycap : Type :=
 | TyCapRegion   : nat -> tycap.
Hint Constructors tycap.


Fixpoint eq_tycap (tc1 : tycap) (tc2 : tycap) : Prop :=
 match tc1, tc2 with
 | TyCapRegion n1, TyCapRegion n2 => eq_nat n1 n1
 end.


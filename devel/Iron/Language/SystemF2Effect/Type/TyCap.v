
Require Export Iron.Language.SystemF2Effect.Kind.


(* Type level capabilities *)
Inductive tycap : Type :=
 | TyCapRegion   : nat -> tycap.
Hint Constructors tycap.


Require Import Iron.Language.SystemF2Data.Type.

(* Literal values. *)
Inductive lit : Type :=
 (* Literal natural number. *)
 | LNat   : nat  -> lit

 (* Literal boolean. *)
 | LBool  : bool -> lit.


Fixpoint typeOfLit (l : lit) : ty := 
 match l with
 | LNat  _   => TCon TyConNat
 | LBool _   => TCon TyConBool
 end.

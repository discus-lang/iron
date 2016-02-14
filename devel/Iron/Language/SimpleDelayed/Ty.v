
Require Export Iron.Language.SimpleDelayed.Base.

(* Types *)
Inductive ty  : Type :=
 | TCon  : nat -> ty           (* data type constructor *)
 | TFun  : ty  -> ty -> ty.    (* function type constructor *)
Hint Constructors ty.


(* Type signatures *)
Inductive sig : Type :=
 | SSig  : nat -> ty -> sig.


(* Type Environments *)
Definition tyenv := list sig.




(* Lookup the type of the given variable from the environment. *)
Fixpoint lookupEnv (var: nat) (te: tyenv) : option ty :=
 match te with
 | nil                => None
 | SSig v t :: rest
    => if beq_nat var v
        then Some t
        else lookupEnv var rest
 end.




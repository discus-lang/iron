
Require Export Iron.Language.SystemF2Effect.Type.Exp.


(* Region identifier is fresh with respect to a type. *)
Fixpoint freshT (p : nat) (tt : ty) : Prop :=
 match tt with
 | TVar _         => True
 | TForall k t    => freshT p t
 | TApp t1 t2     => freshT p t1 /\ freshT p t2
 | TSum t1 t2     => freshT p t1 /\ freshT p t2
 | TBot _         => True
 | TCon0 _        => True
 | TCon1 tc t1    => freshT p t1
 | TCon2 tc t1 t2 => freshT p t1 /\ freshT p t2
 | TCap  (TyCapRegion n) => beq_nat n p = false
 end.

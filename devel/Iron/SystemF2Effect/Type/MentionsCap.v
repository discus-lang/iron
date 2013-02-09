
Require Export Iron.SystemF2Effect.Type.Ty.


Fixpoint mentionsCapT (tc : tycap) (tt : ty) : Prop :=
 match tt with
 | TVar _        => False
 | TForall _ t   => mentionsCapT tc t
 | TApp t1 t2    => mentionsCapT tc t1 \/ mentionsCapT tc t2
 | TSum t1 t2    => mentionsCapT tc t1 \/ mentionsCapT tc t2
 | TBot  _       => False
 | TCon0 _       => False
 | TCon1 _ t1    => mentionsCapT tc t1
 | TCon2 _ t1 t2 => mentionsCapT tc t1 \/ mentionsCapT tc t2
 | TCap  tc'     => eq_tycap tc tc'
 end.


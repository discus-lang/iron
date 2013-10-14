
Require Export Iron.Language.SystemF2Effect.Value.Exp.


Fixpoint freeXV (n : nat) (vv : val) : Prop :=
 match vv with
 | VVar n'            => beq_nat n n' = true
 | VLoc _             => False
 | VLam t x           => freeXX (S n) x
 | VLAM k x           => freeXX n x
 | VConst _           => False
 end
 with   freeXX (n : nat) (xx : exp) : Prop :=
 match xx with
 | XVal     v         => freeXV n v
 | XLet     t x1 x2   => freeXX n x1 \/ freeXX (S n) x2
 | XApp     v1 v2     => freeXV n v1 \/ freeXV n v2
 | XAPP     v1  t2    => freeXV n v1
 | XOp1     op v      => freeXV n v
 | XPrivate x         => freeXX n x
 | XExtend  t x       => freeXX n x
 | XAlloc   t v1      => freeXV n v1
 | XRead    t v1      => freeXV n v1
 | XWrite   t v1 v2   => freeXV n v1 \/ freeXV n v2
 end.



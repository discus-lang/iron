
Require Export Iron.Language.SystemF2Effect.Value.Exp.


Fixpoint FreeXV (n : nat) (vv : val) : Prop :=
 match vv with
 | VVar n'            => n = n'
 | VLoc _             => False
 | VLam t x           => FreeXX (S n) x
 | VLAM k x           => FreeXX n x
 | VConst _           => False
 end
 with   FreeXX (n : nat) (xx : exp) : Prop :=
 match xx with
 | XVal     v         => FreeXV n v
 | XLet     t x1 x2   => FreeXX n x1 \/ FreeXX (S n) x2
 | XApp     v1 v2     => FreeXV n v1 \/ FreeXV n v2
 | XAPP     v1  t2    => FreeXV n v1
 | XOp1     op v      => FreeXV n v
 | XPrivate x         => FreeXX n x
 | XExtend  t x       => FreeXX n x
 | XAlloc   t v1      => FreeXV n v1
 | XRead    t v1      => FreeXV n v1
 | XWrite   t v1 v2   => FreeXV n v1 \/ FreeXV n v2
 end.



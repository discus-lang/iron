
Require Export Iron.Language.SystemF2Effect.Value.Exp.


Fixpoint suppV (l : nat) (vv : val) : Prop := 
 match vv with
 | VVar n'            => False
 | VLoc l'            => l = l'
 | VLam t x           => suppX l x
 | VLAM k x           => suppX l x
 | VConst _           => False
 end
 with   suppX (l : nat) (xx : exp) : Prop :=
 match xx with
 | XVal     v         => suppV l v
 | XLet     t x1 x2   => suppX l x1 \/ suppX l x2
 | XApp     v1 v2     => suppV l v1 \/ suppV l v2
 | XAPP     v1  t2    => suppV l v1
 | XOp1     op v      => suppV l v
 | XPrivate x         => suppX l x
 | XExtend  t x       => suppX l x
 | XAlloc   t v1      => suppV l v1
 | XRead    t v1      => suppV l v1
 | XWrite   t v1 v2   => suppV l v1 \/ suppV l v2
 end.

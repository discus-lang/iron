
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.Exp.


Fixpoint freshV (p : nat) (vv : val) : Prop :=
 match vv with 
 | VVar     _       => True
 | VLoc     _       => True
 | VLam     t x     => freshT p t  /\ freshX p x
 | VLAM     k x     => freshX p x
 | VConst   _       => True
 end
 with    freshX (p : nat) (xx : exp) : Prop :=
 match xx with
 | XVal     v       => freshV p v
 | XLet     t x1 x2 => freshT p t  /\ freshX p x1 /\ freshX p x2
 | XApp     v1 v2   => freshV p v1 /\ freshV p v2
 | XAPP     v1 t2   => freshV p v1 /\ freshT p t2
 | XOp1     op v    => freshV p v
 | XPrivate x       => freshX p x
 | XExtend  t x     => freshT p t  /\ freshX p x
 | XAlloc   t v     => freshT p t  /\ freshV p v
 | XRead    t v     => freshT p t  /\ freshV p v
 | XWrite   t v1 v2 => freshT p t  /\ freshV p v1 /\ freshV p v2
 end.


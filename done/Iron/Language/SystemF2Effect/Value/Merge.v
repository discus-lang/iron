
Require Import Iron.Language.SystemF2Effect.Value.


Fixpoint mergeT (p1 p2 : nat) (tt : ty)  : ty :=
 match tt with
 | TVar    _            => tt
 | TForall k t          => TForall k (mergeT p1 p2 t)
 | TApp    t1 t2        => TApp (mergeT p1 p2 t1) (mergeT p1 p2 t2)
 | TSum    t1 t2        => TSum (mergeT p1 p2 t1) (mergeT p1 p2 t2)
 | TBot    k            => TBot k
 | TCon0   tc0          => TCon0 tc0
 | TCon1   tc1 t1       => TCon1 tc1 (mergeT p1 p2 t1)
 | TCon2   tc2 t1 t2    => TCon2 tc2 (mergeT p1 p2 t1) (mergeT p1 p2 t2)
 | TCap (TyCapRegion p) => if beq_nat p p2 then TRgn p1 else tt
 end.
    

Fixpoint mergeV (p1 p2 : nat) (vv : val) : val :=
 match vv with
 | VVar  _       => vv
 | VLoc  _       => vv
 | VLam  t x     => VLam (mergeT p1 p2 t) (mergeX p1 p2 x)
 | VLAM  k x     => VLAM k (mergeX p1 p2 x)
 | VConst c      => vv
 end
 with   mergeX (p1 p2 : nat) (xx : exp) : exp :=
 match xx with
 | XVal v        => XVal (mergeV p1 p2 v)
 | ...

  


Lemma typev_merge 
 : forall 
 ,  TYPEV ke te se sp v (substTT 0 (TRgn p2) t)
 -> TYPEV ke (mergeTE p1 p2 te) (mergeSE p1 p2 se) sp 
             (mergeV  p1 p2 v)  (substTT 0 (TRgn p1) t).

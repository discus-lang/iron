
Require Import Iron.Language.SystemF2Effect.Value.Exp.
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.


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
 | VVar  _        => vv
 | VLoc  _        => vv
 | VLam  t x      => VLam     (mergeT p1 p2 t) (mergeX p1 p2 x)
 | VLAM  k x      => VLAM k   (mergeX p1 p2 x)
 | VConst c       => vv
 end
 with   mergeX (p1 p2 : nat) (xx : exp) : exp :=
 match xx with
 |  XVal v         
 => XVal     (mergeV p1 p2 v)

 |  XLet t x1 x2   
 => XLet     (mergeT p1 p2 t)  (mergeX p1 p2 x1) (mergeX p1 p2 x2)

 |  XApp v1 v2     
 => XApp     (mergeV p1 p2 v1) (mergeV p1 p2 v2)

 |  XAPP v1 t2     
 => XAPP     (mergeV p1 p2 v1) (mergeT p1 p2 t2)

 |  XOp1 op v      
 => XOp1 op  (mergeV p1 p2 v)

 |  XPrivate x     
 => XPrivate (mergeX p1 p2 x)

 |  XExtend  t x   
 => XExtend  (mergeT p1 p2 t)  (mergeX p1 p2 x)

 |  XAlloc t v     
 => XAlloc   (mergeT p1 p2 t)  (mergeV p1 p2 v)

 |  XRead  t v     
 => XRead    (mergeT p1 p2 t)  (mergeV p1 p2 v)

 |  XWrite t v1 v2 
 => XWrite   (mergeT p1 p2 t)  (mergeV p1 p2 v1) (mergeV p1 p2 v2)
 end.


Definition mergeTE p1 p2 te := map (mergeT p1 p2) te.
Hint Unfold mergeTE.


Definition mergeSE p1 p2 se := map (mergeT p1 p2) se.
Hint Unfold mergeSE.


(********************************************************************)
Lemma typex_merge 
 : forall ix ke te se sp x t e p1 p2
 ,  TYPEX ke te se sp 
          x                 (substTT ix (TRgn p2) t) (substTT ix (TRgn p2) e)
 -> TYPEX ke                (mergeTE p1 p2 te)       (mergeSE p1 p2 se) sp 
          (mergeX  p1 p2 x) (substTT ix (TRgn p1) t) (substTT ix (TRgn p1) e).
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t
      ,  get ix ke = Some KRegion
      -> TYPEV ke te se sp v     (substTT ix (TRgn p2) t)  
      -> TYPEV ke                (mergeTE p1 p2 te) (mergeSE p1 p2 se) sp
               (mergeV  p1 p2 v) (substTT ix (TRgn p1) t));
  intros.

 - Case "VVar".
   admit.

 - Case "VLoc".
   admit.

 - Case "VLam".
   inverts H0.
   destruct t0;       try (snorm; congruence).
   inverts H7.
   destruct t0_1;     try (snorm; congruence).
   simpl in H1. inverts H1.
   destruct t0_1_1;   try (snorm; congruence).
   simpl in H2. inverts H2.
   destruct t0_1_1_1; try (snorm; congruence).
   simpl in H1. inverts H1.
   simpl.
   rrwrite ( mergeT p1 p2 (substTT ix (TRgn p2) t0_1_1_2)
           = substTT ix (TRgn p1) t0_1_1_2) by admit.
   eapply TvLam. 
   + admit.                                  (* fix kind  of TRgn p1 *)
   + eapply IHx in H9; auto.
     simpl in H9.
     admit.

 - Case "VLAM".
   snorm.
   admit.

 - Case "VConst".
   snorm. 
   eapply TvConst.
   destruct c; inverts H0; snorm.
   + destruct t; snorm; nope.
   + destruct t; snorm; nope.
   + destruct t; snorm; nope.

 - Case "VVal".
   admit.

 - Case "XLet".
   admit.

 - Case "XApp".
   admit.

 - Case "XAPP".
   admit.

 - Case "XOp1".
   admit.

 - Case "XPrivate".
   admit.

 - Case "XExtend".
   admit.

 - Case "XAlloc".
   admit.

 - Case "XRead".
   admit.

 - Case "XWrite".
   admit.
Qed.



Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.


(** * Single Small Step Evaluation *)
(** The single step rules model the individual transitions that the 
     machine can make at runtime. *)

Inductive STEP : store -> exp -> store -> exp -> Prop :=

 (* Step an expression in the let context. *)
 | EsLet 
   :  forall t s x1 x2 s' x1'
   ,  STEP s x1             s' x1'
   -> STEP s  (XLet t x1 x2) 
           s' (XLet t x1' x2)

 (* Let substitution. *)
 | EsLetSubst
   :  forall t s v x2
   ,  STEP s (XLet t (XVal v) x2) 
           s (substVX 0 v x2)

 (* Value application. *)
 | EsAppSubst
   : forall s t11 x12 v2
   ,  STEP s (XApp (VLam t11 x12) v2)
           s (substVX 0 v2 x12)

 (* Type application. *)
 | EsLAMSubst
   :  forall s k11 x12 t2      
   ,  STEP s (XAPP (VLAM k11 x12) t2)
           s (substTX 0 t2 x12)

 (* Allocate a reference. *) 
 | EsAlloc
   :  forall s r1 v1
   ,  STEP s (XAlloc (TCon (TyConRegion r1)) v1)
           (snoc (SBind r1 v1) s) (XVal (VLoc (length s)))

 (* Read from a reference. *)
 | EsRead
   :  forall s l v r
   ,  get l s = Some (SBind r v)
   -> STEP s (XRead (TCon (TyConRegion r)) (VLoc l)) s (XVal v)

 (* Write to a reference. *)
 | EsWrite 
   :  forall s l r v
   ,  STEP s (XWrite (TCon (TyConRegion r)) (VLoc l) v) 
           (update l (SBind r v) s)  (XVal (VConst CUnit))

 (* Take the successor of a natural. *)
 | EsSucc
   :  forall s n
   ,  STEP s  (XOp1 OSucc (VConst (CNat n)))
           s  (XVal (VConst (CNat (S n))))

 (* Test a natural for zero. *)
 | EsIsZeroTrue 
   :  forall s n
   ,  STEP s  (XOp1 OIsZero (VConst (CNat n)))
           s  (XVal (VConst (CBool (beq_nat n 0)))).

Hint Constructors STEP.



Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.TyJudge.
Require Export Iron.Language.SystemF2Effect.SubstValExp.
Require Export Iron.Language.SystemF2Effect.Va.

(********************************************************************)
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
   :  forall s t1 v1
   ,  STEP s           (XAlloc t1 v1)
           (snoc v1 s) (XVal (VLoc (length s)))

 (* Read from a reference. *)
 | EsRead
   :  forall s l v 
   ,  get l s = Some v
   -> STEP s (XRead (VLoc l)) s (XVal v)

 (* Write to a reference. *)
 | EsWrite 
   :  forall s l v
   ,  STEP s               (XWrite (VLoc l) v) 
           (update l v s)  (XVal (VConst CUnit)).

Hint Constructors STEP.

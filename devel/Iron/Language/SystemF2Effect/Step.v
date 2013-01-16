
Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.


(** * Single Small Step Evaluation *)
(** The single step rules model the individual transitions that the 
     machine can make at runtime. *)

Inductive 
  STEP :  store -> stprops -> exp 
       -> store -> stprops -> exp 
       -> Prop :=

 (* Step an expression in the let context. *)
 | EsLet 
   :  forall ss sp ss' sp' t x1 x1' x2
   ,  STEP ss sp x1 ss' sp' x1'
   -> STEP ss  sp   (XLet t x1  x2) 
           ss' sp'  (XLet t x1' x2)

 (* Let substitution. *)
 | EsLetSubst
   :  forall ss sp t v x2
   ,  STEP ss sp    (XLet t (XVal v) x2) 
           ss sp    (substVX 0 v x2)

 (* Value application. *)
 | EsAppSubst
   :  forall ss sp t11 x12 v2
   ,  STEP ss sp    (XApp (VLam t11 x12) v2)
           ss sp    (substVX 0 v2 x12)

 (* Type application. *)
 | EsLAMSubst
   :  forall ss sp k11 x12 t2      
   ,  STEP ss sp    (XAPP (VLAM k11 x12) t2)
           ss sp    (substTX 0 t2 x12)

 (* Create a new region. *)
 | EsNew
   :  forall ss sp x
   ,  STEP ss sp              (XNew x) 
           ss (SRegion <: sp) (XUse (length sp) (substTX 0 (TCap (TyCapRegion (length sp))) x))

 (* Evaluation with a region. *)
 | EsUse
   :  forall ss sp ss' sp' x x' n
   ,  STEP ss sp x ss' sp' x'
   -> STEP ss  sp   (XUse n x) 
           ss' sp'  (XUse n x')

 (* Pop a region from the stack. *)
 | EsUsePop
   :  forall ss sp n v
   ,  STEP ss  sp   (XUse n (XVal v)) 
           ss  sp   (XVal v)
   (* TODO: pop bindings and handle for the numbered region.
            set dealloc props and bind to some other val. *)

 (* Allocate a reference. *) 
 | EsAlloc
   :  forall ss sp r1 v1
   ,  STEP ss                    sp (XAlloc (TCap (TyCapRegion r1)) v1)
           (StValue r1 v1 <: ss) sp (XVal (VLoc (length ss)))

 (* Read from a reference. *)
 | EsRead
   :  forall ss sp l v r
   ,  get l ss = Some (StValue r v)
   -> STEP ss sp    (XRead (TCap (TyCapRegion r)) (VLoc l)) 
           ss sp    (XVal v)

 (* Write to a reference. *)
 | EsWrite 
   :  forall ss sp l r v
   ,  STEP ss sp    (XWrite (TCap (TyCapRegion r)) (VLoc l) v)
           (update l (StValue r v) ss) sp (XVal (VConst CUnit))

 (* Take the successor of a natural. *)
 | EsSucc
   :  forall ss sp n
   ,  STEP ss sp    (XOp1 OSucc (VConst (CNat n)))
           ss sp    (XVal (VConst (CNat (S n))))

 (* Test a natural for zero. *)
 | EsIsZeroTrue 
   :  forall ss sp n
   ,  STEP ss sp    (XOp1 OIsZero (VConst (CNat n)))
           ss sp    (XVal (VConst (CBool (beq_nat n 0)))).

Hint Constructors STEP.


(* When we step the expression the resulting set of store properties
   is at least as big as the initial ones. *)
Lemma step_stprops_extends
 :  forall ss ss' sp sp' x x'
 ,  STEP ss sp x ss' sp' x'
 -> extends sp' sp.
Proof.
 intros. induction H; eauto.
Qed.
Hint Resolve step_stprops_extends.


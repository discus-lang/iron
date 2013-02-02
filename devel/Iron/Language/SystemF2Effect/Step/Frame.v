
Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.


(* Frame Stacks *)
Inductive frame : Set :=
 (* Holds the continuation of a let-expression while the right
    of the binding is being evaluated. *)
 | FLet : ty -> exp -> frame

 (* Holds the continuation of a use-expression while the body
    evaluates inside a fresh region *)
 | FUse : nat -> frame.
Hint Constructors frame.

Definition stack := list frame.
Hint Unfold stack.

Definition allocRegionFs (fs : stack) : nat
 := 0.

(********************************************************************)
(* Pure reductions that don't depend on the context. *)
Inductive 
 STEPP : exp -> exp -> Prop :=
 (* Value application. *)
 | SpAppSubst
   : forall t11 x12 v2
   , STEPP (XApp (VLam t11 x12) v2)
           (substVX 0 v2 x12)

 (* Type application. *)
 | EpAPPSubst
   : forall k11 x12 t2      
   , STEPP (XAPP (VLAM k11 x12) t2)
           (substTX 0 t2 x12)

 (* Take the successor of a natural. *)
 | EpSucc
   :  forall n
   ,  STEPP (XOp1 OSucc (VConst (CNat n)))
            (XVal (VConst (CNat (S n))))

 (* Test a natural for zero. *)
 | EsIsZeroTrue 
   :  forall n
   ,  STEPP (XOp1 OIsZero (VConst (CNat n)))
            (XVal (VConst (CBool (beq_nat n 0)))).


(********************************************************************)
(* Context sensitive reductions. *)
Inductive 
 STEPF :  store -> stack -> exp 
       -> store -> stack -> exp 
       -> Prop :=

 (* Pure evaluation *****************************)
 (* Pure evaluation in a context. *)
 | SfStep
   :  forall ss fs x x'
   ,  STEPP        x        x'
   -> STEPF  ss fs x' ss fs x'

 (* Let contexts ********************************)
 (* Push the continuation for a let-expression onto the stack. *)
 | SfLetPush
   :  forall ss fs t x1 x2
   ,  STEPF  ss  fs               (XLet t x1 x2)
             ss (fs :> FLet t x2) x1

 (* Substitute value of the bound variable into the let body. *)
 | SfLetPop
   :  forall ss  fs t v1 x2
   ,  STEPF  ss (fs :> FLet t x2)  (XVal v1)
             ss  fs                (substVX 0 v1 x2)

 (* Region operators ****************************)
 (* Create a new region. *)
 | SfRegionNew
   :  forall ss  fs x p
   ,  p = allocRegionFs fs 
   -> STEPF  ss  fs                (XNew x)
             ss (fs :> FUse p)     (substTX 0 (TCap (TyCapRegion p)) x)

 (* Pop a region from the stack. *)
 | SfRegionPop
   :  forall ss  fs v1 p
   ,  STEPF  ss (fs :> FUse p)     (XVal v1)
             ss  fs                (XVal v1)

 (* Store operators *****************************)
 (* Allocate a reference. *) 
 | SfStoreAlloc
   :  forall ss fs r1 v1
   ,  STEPF  ss                    fs (XAlloc (TCap (TyCapRegion r1)) v1)
             (StValue r1 v1 <: ss) fs (XVal (VLoc (length ss)))

 (* Read from a reference. *)
 | SfStoreRead
   :  forall ss fs l v r
   ,  get l ss = Some (StValue r v)
   -> STEPF ss fs                 (XRead (TCap (TyCapRegion r))  (VLoc l)) 
            ss fs                 (XVal v)

 (* Write to a reference. *)
 | SfStoreWrite
   :  forall ss fs l r v
   ,  STEPF  ss fs                (XWrite (TCap (TyCapRegion r)) (VLoc l) v)
             (update l (StValue r v) ss) fs (XVal (VConst CUnit)).





Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.
Require Export Iron.Language.SystemF2Effect.Step.Pure.
Require Export Iron.Language.SystemF2Effect.Store.Prop.


(********************************************************************)
(* Frames *)
Inductive frame : Set :=
 (* Holds the continuation of a let-expression while the right
    of the binding is being evaluated. *)
 | FLet   : ty  -> exp      -> frame

 (* Private region.
    If the first argument is some region identifier then this new
    private region will be merged with that one when leaving its scope, 
    otherwise the region is deallocated. *)
 | FPriv  : option nat -> nat -> frame.
Hint Constructors frame.


Definition isFPriv (p2 : nat) (f : frame)
 := exists p1, f = FPriv p1 p2.
Hint Unfold isFPriv.


(* Frame stacks *)
Definition stack := list frame.
Hint Unfold stack.


(********************************************************************)
(* Context sensitive reductions. *)
Inductive 
 StepF :  store -> stprops -> stack -> exp 
       -> store -> stprops -> stack -> exp 
       -> Prop :=

 (* Pure evaluation *****************************)
 (* Pure evaluation in a context. *)
 | SfStep
   :  forall ss sp fs x x'
   ,  StepP           x           x'
   -> StepF  ss sp fs x  ss sp fs x'

 (* Let contexts ********************************)
 (* Push the continuation for a let-expression onto the stack. *)
 | SfLetPush
   :  forall ss sp fs t x1 x2
   ,  StepF  ss sp  fs               (XLet t x1 x2)
             ss sp (fs :> FLet t x2)  x1

 (* Substitute value of the bound variable into the let body. *)
 | SfLetPop
   :  forall ss sp  fs t v1 x2
   ,  StepF  ss sp (fs :> FLet t x2) (XVal v1)
             ss sp  fs               (substVX 0 v1 x2)

 (* Region operators ****************************)
 (* Create a private region. *)
 | SfPrivatePush
   :  forall ss sp fs x p
   ,  p = allocRegion sp
   -> StepF  ss sp                       fs                  (XPrivate x)
             ss (SRegion p <: sp)       (fs :> FPriv None p) (substTX 0 (TRgn p) x)

 (* Pop the frame for a private region and delete it from the heap. *)
 | SfPrivatePop
   :  forall ss sp  fs v1 p
   ,  StepF  ss                         sp (fs :> FPriv None p) (XVal v1)
             (map (deallocRegion p) ss) sp  fs                  (XVal v1)

 (* Begin extending an existing region. *)
 | SfExtendPush
   :  forall ss sp fs x p1 p2
   ,  p2 = allocRegion sp
   -> StepF ss sp                  fs                        (XExtend (TRgn p1) x)
            ss (SRegion p2 <: sp) (fs :> FPriv (Some p1) p2) (substTX 0 (TRgn p2) x)

 (* Pop the frame for a region extension and merge it with the existing one. *)
 | SfExtendPop
   :  forall ss sp fs p1 p2 v1
   ,  StepF  ss                      sp (fs :> FPriv (Some p1) p2) (XVal v1)
             (map (mergeB p1 p2) ss) sp fs                   (XVal (mergeV p1 p2 v1))

 (* Store operators *****************************)
 (* Allocate a reference. *) 
 | SfStoreAlloc
   :  forall ss sp fs p1 v1
   ,  StepF  ss                    sp  fs (XAlloc (TRgn p1) v1)
             (StValue p1 v1 <: ss) sp  fs (XVal (VLoc (length ss)))

 (* Read from a reference. *)
 | SfStoreRead
   :  forall ss sp fs l v p
   ,  get l ss = Some (StValue p v)
   -> StepF ss                     sp  fs (XRead (TRgn p)  (VLoc l)) 
            ss                     sp  fs (XVal v)

 (* Write to a reference. *)
 | SfStoreWrite
   :  forall ss sp fs l p v1 v2 
   ,  get l ss = Some (StValue p v1)
   -> StepF  ss sp fs                 (XWrite (TRgn p) (VLoc l) v2)
             (update l (StValue p v2) ss) sp fs (XVal (VConst CUnit)).

Hint Constructors StepF.



(********************************************************************)
Lemma stepF_extends_stprops
 :  forall  ss1 sp1 fs1 x1  ss2 sp2 fs2 x2
 ,  StepF   ss1 sp1 fs1 x1  ss2 sp2 fs2 x2
 -> extends sp2 sp1.
Proof.
 intros. 
 induction H; eauto.
Qed.


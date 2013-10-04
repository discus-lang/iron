
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

 (* Private region. *)
 | FPriv  : nat -> frame

 (* Region extension.
    The first region is being extended with the second. *)
 | FExt   : nat -> nat -> frame.
Hint Constructors frame.


Definition isFPriv (p : nat) (f : frame)
 := f = FPriv p.
Hint Unfold isFPriv.


Definition isFExt  (p1 p2 : nat) (f : frame)
 := f = FExt p1 p2.


(* Frame stacks *)
Definition stack := list frame.
Hint Unfold stack.


(********************************************************************)
(* Context sensitive reductions. *)
Inductive 
 STEPF :  store -> stprops -> stack -> exp 
       -> store -> stprops -> stack -> exp 
       -> Prop :=

 (* Pure evaluation *****************************)
 (* Pure evaluation in a context. *)
 | SfStep
   :  forall ss sp fs x x'
   ,  STEPP           x           x'
   -> STEPF  ss sp fs x  ss sp fs x'

 (* Let contexts ********************************)
 (* Push the continuation for a let-expression onto the stack. *)
 | SfLetPush
   :  forall ss sp fs t x1 x2
   ,  STEPF  ss sp  fs               (XLet t x1 x2)
             ss sp (fs :> FLet t x2)  x1

 (* Substitute value of the bound variable into the let body. *)
 | SfLetPop
   :  forall ss sp  fs t v1 x2
   ,  STEPF  ss sp (fs :> FLet t x2) (XVal v1)
             ss sp  fs               (substVX 0 v1 x2)

 (* Region operators ****************************)
 (* Create a private region. *)
 | SfPrivatePush
   :  forall ss sp fs x p
   ,  p = allocRegion sp
   -> STEPF  ss sp                 fs              (XPrivate x)
             ss (SRegion p <: sp) (fs :> FPriv p)  (substTX 0 (TRgn p) x)

 (* Pop the frame for a private region and delete it from the heap. *)
 | SfPrivatePop
   :  forall ss sp  fs v1 p
   ,  STEPF  ss                      sp (fs :> FPriv p)(XVal v1)
             (map (deallocate p) ss) sp  fs            (XVal v1)

 (* Begin extending an existing region. *)
 | SfExtendPush
   :  forall ss sp fs x p1 p2
   ,  p2 = allocRegion sp
   -> STEPF ss sp                  fs                (XExtend (TRgn p1) x)
            ss (SRegion p2 <: sp) (fs :> FExt p1 p2) (substTX 0 (TRgn p2) x)

 (* Pop the frame for a region extension and merge it with the existing one. *)
 | SfExtendPop
   :  forall ss sp fs p1 p2 v1
   ,  STEPF  ss                      sp (fs :> FExt p1 p2) (XVal v1)
             (map (mergeB p1 p2) ss) sp fs                 (XVal v1)

 (* Store operators *****************************)
 (* Allocate a reference. *) 
 | SfStoreAlloc
   :  forall ss sp fs r1 v1
   ,  STEPF  ss                    sp  fs (XAlloc (TRgn r1) v1)
             (StValue r1 v1 <: ss) sp  fs (XVal (VLoc (length ss)))

 (* Read from a reference. *)
 | SfStoreRead
   :  forall ss sp fs l v r
   ,  get l ss = Some (StValue r v)
   -> STEPF ss                     sp  fs (XRead (TRgn r)  (VLoc l)) 
            ss                     sp  fs (XVal v)

 (* Write to a reference. *)
 | SfStoreWrite
   :  forall ss sp fs l r v1 v2 
   ,  get l ss = Some (StValue r v1)
   -> STEPF  ss sp fs                 (XWrite (TRgn r) (VLoc l) v2)
             (update l (StValue r v2) ss) sp fs (XVal (VConst CUnit)).

Hint Constructors STEPF.


(********************************************************************)
Lemma stepf_extends_stprops
 :  forall  ss1 sp1 fs1 x1  ss2 sp2 fs2 x2
 ,  STEPF   ss1 sp1 fs1 x1  ss2 sp2 fs2 x2
 -> extends sp2 sp1.
Proof.
 intros. 
 induction H; eauto.
Qed.


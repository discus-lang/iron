
Require Export Iron.SystemF2Effect.Type.
Require Export Iron.SystemF2Effect.Value.
Require Export Iron.SystemF2Effect.Step.Pure.
Require Export Iron.SystemF2Effect.Store.Prop.


(********************************************************************)
(* Frame Stacks *)
Inductive frame : Set :=
 (* Holds the continuation of a let-expression while the right
    of the binding is being evaluated. *)
 | FLet   : ty  -> exp      -> frame

 (* Local region. *)
 | FUse   : nat -> frame.
Hint Constructors frame.

Definition stack := list frame.
Hint Unfold stack.


Definition isFUse (p : nat) (f : frame)
 := f = FUse p.
Hint Unfold isFUse.


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
 (* Create a new region. *)
 | SfRegionNew
   :  forall ss sp fs x p
   ,  p = allocRegion sp
   -> STEPF  ss sp                 fs            (XNew x)
             ss (SRegion p <: sp) (fs :> FUse p) (substTX 0 (TCap (TyCapRegion p)) x)

 (* Pop a region from the stack. *)
 | SfRegionPop
   :  forall ss sp  fs v1 p
   ,  STEPF  ss                      sp (fs :> FUse p)    (XVal v1)
             (map (deallocate p) ss) sp  fs               (XVal v1)

 (* Store operators *****************************)
 (* Allocate a reference. *) 
 | SfStoreAlloc
   :  forall ss sp fs r1 v1
   ,  STEPF  ss                    sp  fs (XAlloc (TCap (TyCapRegion r1)) v1)
             (StValue r1 v1 <: ss) sp  fs (XVal (VLoc (length ss)))

 (* Read from a reference. *)
 | SfStoreRead
   :  forall ss sp fs l v r
   ,  get l ss = Some (StValue r v)
   -> STEPF ss                     sp  fs (XRead (TCap (TyCapRegion r))  (VLoc l)) 
            ss                     sp  fs (XVal v)

 (* Write to a reference. *)
 | SfStoreWrite
   :  forall ss sp fs l r v1 v2 
   ,  get l ss = Some (StValue r v1)
   -> STEPF  ss sp fs                 (XWrite (TCap (TyCapRegion r)) (VLoc l) v2)
             (update l (StValue r v2) ss) sp fs (XVal (VConst CUnit)).

Hint Constructors STEPF.


(******************************************************************************)
Lemma stepf_stprops_extends
 :  forall  ss1 sp1 fs1 x1  ss2 sp2 fs2 x2
 ,  STEPF   ss1 sp1 fs1 x1  ss2 sp2 fs2 x2
 -> extends sp2 sp1.
Proof.
 intros. 
 induction H; eauto.
Qed.


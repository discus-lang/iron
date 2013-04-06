
Require Export Iron.SystemF2Effect.Step.Frame.
Require Export Iron.SystemF2Effect.Store.Bind.
Require Export Iron.SystemF2Effect.Store.TypeB.
Require Export Iron.SystemF2Effect.Store.TypeS.
Require Export Iron.SystemF2Effect.Store.StoreM.
Require Export Iron.SystemF2Effect.Store.StoreP.


(* Well formed store. *)
Definition WfS  (se: stenv) (sp: stprops)  (ss: store)
 := Forall ClosedT se
 /\ STOREM se    ss
 /\ STORET se sp ss.
Hint Unfold WfS.


(* Well formed store and frame stack. *)
Definition WfFS (se : stenv) (sp : stprops) (ss : store) (fs : stack) 
 := Forall ClosedT se
 /\ STOREM se ss
 /\ STORET se sp ss
 /\ STOREP sp fs.


Lemma wfFS_wfS 
 :  forall se sp ss fs
 ,  WfFS   se sp ss fs
 -> WfS    se sp ss.
Proof. firstorder. Qed.


Lemma wfFS_fuse_sregion
 :  forall se sp ss fs p
 ,  WfFS se sp ss fs
 -> In (FUse p)    fs
 -> In (SRegion p) sp.
Proof. firstorder. Qed.


Lemma wfFS_storem_length
 :  forall se sp ss fs
 ,  WfFS   se sp ss fs
 -> length se = length ss.
Proof.
 intros.
 inverts H. rip.
Qed.
Hint Resolve wfFS_storem_length.


(* Weaken frame stack in WfFS *)
Lemma wfFS_sregion_cons
 :  forall se sp ss fs p
 ,  WfFS se sp ss fs
 -> WfFS se (sp :> SRegion p) ss (fs :> FUse p).
Proof. 
 intros.
 unfold WfFS. 
 inverts H. inverts H1. inverts H2.
 auto.
Qed.
Hint Resolve wfFS_sregion_cons.


(* Deallocating a region preserves well-formedness of the store. *)
Lemma wfFS_stack_pop
 :  forall se sp ss fs p
 ,  WfFS se sp ss               (fs :> FUse p)
 -> WfFS se sp (deallocate p ss) fs.
Proof.
 intros.
 unfold WfFS in *. 
 admit. (* wfFS after region dealloc *)
(*
 rip. 
 unfold STOREP in *.
  eauto.
*)
Qed.


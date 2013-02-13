
Require Export Iron.SystemF2Effect.Store.Bind.
Require Export Iron.SystemF2Effect.Step.Frame.


(******************************************************************************)
(* Store typing models the store.
   All types in the store typing have a corresponding binding in the store.
   We don't want entries in the store typing that don't have corresponding
   bindings in the store. *)

Definition STOREM (se: stenv) (ss: store)
 := length se = length ss.
Hint Unfold STOREM.


(* Extended store environment models the extended store *)
Lemma storem_snoc
 :  forall se ss t stv
 ,  STOREM se ss
 -> STOREM (t <: se) (stv <: ss).
Proof.
 intros.
 unfold STOREM.
 have (length se = length ss). 
 burn.
Qed.
Hint Resolve storem_snoc.


(*****************************************************************************)
(* All region handles on frame stack are in store properties.

   We don't require the other way, forcing all store properties to be in 
   the frame stack. This is because we need to be able to pop a Use frame and
   still have any region handles in the expression being well typed, along with
   dangling references into that region. *)

Definition STOREP  (sp : stprops) (fs : stack)
 := forall n, In (FUse n) fs -> In (SRegion n) sp.


(* Weaken frame stack in store properties. *)
Lemma storep_cons
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (sp :> SRegion p) (fs :> FUse p).
Proof.
 unfold STOREP in *.
 - intros.
   have HN: (n = p \/ ~(n = p)).
   inverts HN.
   + simpl. auto.
   + assert (In (FUse n) fs).
      eapply in_tail.
      have (FUse n <> FUse p) by congruence.
      eauto. auto.
     eapply in_split.
      left. eapply H. auto.
Qed.
Hint Resolve storep_cons.


(******************************************************************************)
(* Well formed store. *)
Definition WfS  (se: stenv) (sp: stprops)  (ss: store)
 := Forall closedT se
 /\ STOREM se    ss
 /\ STORET se sp ss.
Hint Unfold WfS.


(* Well formed store and frame stack. *)
Definition WfFS (se : stenv) (sp : stprops) (ss : store) (fs : stack) 
 := Forall closedT se
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


(* Popping a frame from the stack preserves well formedness. *)
Lemma wfFS_stack_pop
 :  forall se sp ss fs p
 ,  WfFS se sp ss (fs :> FUse p)
 -> WfFS se sp ss fs.
Proof.
 intros.
 unfold WfFS in *. rip. 
 unfold STOREP in *.
  eauto.
Qed.


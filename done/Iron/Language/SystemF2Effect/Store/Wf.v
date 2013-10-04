
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.Bind.
Require Export Iron.Language.SystemF2Effect.Store.TypeB.
Require Export Iron.Language.SystemF2Effect.Store.StoreT.
Require Export Iron.Language.SystemF2Effect.Store.StoreM.
Require Export Iron.Language.SystemF2Effect.Store.StoreP.


(*******************************************************************)
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


(*******************************************************************)
Lemma wfFS_wfS 
 :  forall se sp ss fs
 ,  WfFS   se sp ss fs
 -> WfS    se sp ss.
Proof. firstorder. Qed.


Lemma wfFS_fpriv_sregion
 :  forall se sp ss fs p
 ,  WfFS se sp ss fs
 -> In (FPriv p)   fs
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


(* Creating a private region preserves well-formedness of the store. *)
Lemma wfFS_region_priv
 :  forall se sp ss fs p
 ,  WfFS se sp ss fs
 -> WfFS se (SRegion p <: sp) ss (fs :> FPriv p).
Proof. 
 intros.
 unfold WfFS in *. 
 inverts H. inverts H1. inverts H2.
 auto.
Qed.
Hint Resolve wfFS_region_priv.


(* Creating an extension region preserves well-formedness of the store. *)
Lemma wfFS_region_ext
 :  forall se sp ss fs p1 p2
 ,  WfFS  se  sp ss fs
 -> KindT nil sp (TRgn p1) KRegion
 -> In (SRegion p1) sp
 -> WfFS  se  (SRegion p2 <: sp) ss (fs :> FExt p1 p2).
Proof.
 intros.
 unfold WfFS in *. 
 unfold STOREP in *. rip.
 - inverts H2.
   nope. rip.
 - inverts H2. 
   inverts H7. rip. eauto.
 - inverts H2.
   inverts H7. eauto. eauto.
Qed. 
Hint Resolve wfFS_region_ext.


(* Deallocating a region preserves well-formedness of the store. *)
Lemma typeb_deallocate
 :  forall ke te se sp p b t
 ,  TYPEB  ke te se sp b t
 -> TYPEB  ke te se sp (deallocate p b) t.
Proof.
 intros.
 destruct b.
 - snorm. subst.
   inverts H. eauto.
 - snorm.
Qed.


Lemma storet_deallocate
 :  forall se sp ss p
 ,  STORET se sp ss
 -> STORET se sp (map (deallocate p) ss).
Proof.
 intros.
 unfold STORET in *.
 eapply Forall2_map_left.
 eapply Forall2_impl.
  intros.
  eapply typeb_deallocate. eauto. auto.
Qed.


(* Deallocating the region mentioned in a use frame on the stop
   of the stack preserves the well formedness of the store. *)
Lemma wfFS_region_deallocate
 :  forall se sp ss fs p
 ,  WfFS se sp ss                     (fs :> FPriv p)
 -> WfFS se sp (map (deallocate p) ss) fs.
Proof.
 intros.
 unfold WfFS in *. rip.
 - unfold STOREM in *.
   rewrite map_length. auto.

 - eapply storet_deallocate. auto.
 
 - unfold STOREP in *. snorm.
 - unfold STOREP in *. snorm. eauto.
 - unfold STOREP in *. snorm. eauto.
Qed.


(* Appending a closed store binding to the store preserves its 
   well formedness. *)
Lemma wfFS_stbind_snoc
 :  forall se sp ss fs p v t
 ,  KindT  nil sp (TRgn p) KRegion
 -> TYPEV  nil nil se sp v t
 -> WfFS           se sp ss fs
 -> WfFS   (TRef (TRgn p) t <: se) sp 
           (StValue p v <: ss) fs.
Proof.
 intros.
 unfold WfFS.
 inverts H1. rip.
 snorm.
 rrwrite ( TRef (TRgn p) t <: se
        = (TRef (TRgn p) t <: nil) >< se) in H4.
 apply in_app_split in H4.
 inverts H4.
 - snorm.
 - snorm.
   inverts H6.
   + have (ClosedT t).
     have (ClosedT (TRgn p)).
     eauto.
   + nope.
 - unfold STOREP in *. rip.
 - unfold STOREP in *. rip. eauto.
 - unfold STOREP in *. rip. eauto.
Qed.
Hint Resolve wfFS_stbind_snoc.


(* Store with an updated binding is still well formed. *)
Lemma wfFS_stbind_update
 :  forall se sp ss fs l p v t
 ,  get l se = Some (TRef (TRgn p) t)
 -> KindT nil sp (TRgn p) KRegion
 -> TYPEV nil nil se sp v t
 -> WfFS se sp ss fs
 -> WfFS se sp (update l (StValue p v) ss) fs.
Proof.
 intros se sp ss fs l p v t HG HK HV HWF1.
 inverts HWF1. rip.
 - have (length se = length ss).
   unfold STOREM.
   rewritess.
   rewrite update_length. auto.
 - unfold STORET.
   eapply Forall2_update_right; eauto.
 - unfold STOREP in *. rip.
 - unfold STOREP in *. rip. eauto.
 - unfold STOREP in *. rip. eauto.
Qed.


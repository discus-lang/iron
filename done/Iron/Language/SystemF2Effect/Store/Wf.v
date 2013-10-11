
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.Bind.
Require Export Iron.Language.SystemF2Effect.Store.TypeB.
Require Export Iron.Language.SystemF2Effect.Store.StoreT.
Require Export Iron.Language.SystemF2Effect.Store.StoreM.
Require Export Iron.Language.SystemF2Effect.Store.StoreP.


(*******************************************************************)
(* Well formed store. *)
Inductive WfS   : stenv -> stprops -> store -> Prop :=
 | WfS_
   :  forall se sp ss
   ,  Forall ClosedT se
   -> STOREM se    ss
   -> STORET se sp ss
   -> WfS se sp ss.
Hint Constructors WfS.


(* Well formed store and frame stack. *)
Inductive WfFS : stenv -> stprops -> store -> stack -> Prop := 
 | WfFS_
   :  forall se sp ss fs
   ,  Forall ClosedT se
   -> STOREM se ss
   -> STORET se sp ss
   -> STOREP sp fs
   -> WfFS se sp ss fs.
Hint Constructors WfFS.


(*******************************************************************)
(* If a well formed frame stack and store is well formed,
   then the store is also well formed by itself. *)
Lemma wfFS_wfS 
 :  forall se sp ss fs
 ,  WfFS   se sp ss fs
 -> WfS    se sp ss.
Proof. intros. inverts H. eauto. Qed.


Lemma wfFS_closedT
 :  forall se sp ss fs
 ,  WfFS   se sp ss fs
 -> Forall ClosedT se.
Proof. intros. inverts H. eauto. Qed.
Hint Resolve wfFS_closedT.


(* The region handles of private regions are present in the
   store properties. *)
Lemma wfFS_fpriv_sregion
 :  forall se sp ss fs m1 p2
 ,  WfFS se sp ss fs
 -> In (FPriv   m1 p2) fs
 -> In (SRegion p2)    sp.
Proof. intros. inverts H. firstorder. Qed.


(* The length of the store enviroment is the same as the length
   of the store. We have one entry in the store environment for
   each binding in the store. *)
Lemma wfFS_storem_length
 :  forall se sp ss fs
 ,  WfFS   se sp ss fs
 -> length se = length ss.
Proof. intros. inverts H. auto. Qed.
Hint Resolve wfFS_storem_length.


(* Creating a top level private region preserves well-formedness
   of the store. *)
Lemma wfFS_push_priv_top
 :  forall se sp ss fs p2
 ,  WfFS se sp ss fs
 -> WfFS se (SRegion p2 <: sp) ss (fs :> FPriv None p2).
Proof. intros. inverts H. auto. Qed.
Hint Resolve wfFS_push_priv_top.


(* Creating an extension region preserves well-formedness 
   of the store. *)
Lemma wfFS_push_priv_ext
 :  forall se sp ss fs p1 p2
 ,  KindT nil sp (TRgn p1) KRegion
 -> In (SRegion p1) sp
 -> WfFS  se  sp ss fs
 -> WfFS  se  (SRegion p2 <: sp) ss (fs :> FPriv (Some p1) p2).
Proof.
 intros.
 inverts H1. eapply WfFS_; rip.
 unfold STOREP in *. rip.
 - inverts H1; eauto. 
   inverts H5. eauto.
 - inverts H1; eauto.
   inverts H5; eauto.
Qed. 
Hint Resolve wfFS_push_priv_ext.


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


(* Deallocating bindings preserves the well typedness of the store. *)
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


(* Deallocating top-level region on the top of the frame stack
   preserves the well formedness of the store. *)
Lemma wfFS_region_deallocate
 :  forall se sp ss fs p
 ,  WfFS se sp ss                     (fs :> FPriv None p)
 -> WfFS se sp (map (deallocate p) ss) fs.
Proof.
 intros.
 inverts H. eapply WfFS_; rip.
 - unfold STOREM in *.
   rewrite map_length; auto.
 - eapply storet_deallocate; auto.
 - unfold STOREP in *; snorm; eauto.
Qed.


Lemma wfFS_pop_priv_ext
 :  forall se sp ss fs p1 p2
 ,  In (SRegion p1) sp
 -> WfFS se sp ss (fs :> FPriv (Some p1) p2)
 -> WfFS (mergeTE p1 p2 se) sp (mergeBs p1 p2 ss) fs.
Proof.
 intros.
 inverts H0. split.
 - eapply Forall_map.
   eapply Forall_impl with (P := ClosedT).
   + intros. eapply mergeT_wfT; eauto.
   + auto.

 - unfold STOREM in *.
   unfold mergeTE. 
   unfold mergeBs.
   repeat (rewrite map_length). auto.

 - unfold STORET.
   eapply storeT_mergeB; auto.
   
 - eapply storep_pop; eauto.
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
 inverts H1. eapply WfFS_; rip.
 inverts_kind.
 snorm.
 rrwrite ( TRef (TRgn p) t <: se
        = (TRef (TRgn p) t <: nil) >< se) in H.
 apply in_app_split in H.
 inverts H.
 - snorm.
 - snorm.
   inverts H1.
   + have (ClosedT t).
     have (ClosedT (TRgn p)).
     eauto.
   + nope.
Qed.
Hint Resolve wfFS_stbind_snoc.


(* Updating bindings preserves the well formedness of the store. *)
Lemma wfFS_stbind_update
 :  forall se sp ss fs l p v t
 ,  get l se = Some (TRef (TRgn p) t)
 -> KindT nil sp (TRgn p) KRegion
 -> TYPEV nil nil se sp v t
 -> WfFS se sp ss fs
 -> WfFS se sp (update l (StValue p v) ss) fs.
Proof.
 intros se sp ss fs l p v t HG HK HV HWF1.
 inverts HWF1. eapply WfFS_; rip.
 - have (length se = length ss).
   unfold STOREM.
   rewritess.
   rewrite update_length. auto.
 - unfold STORET.
   eapply Forall2_update_right; eauto.
Qed.


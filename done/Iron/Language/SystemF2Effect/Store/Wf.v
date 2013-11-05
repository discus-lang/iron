
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
   -> StoreM se    ss
   -> StoreT se sp ss
   -> WfS se sp ss.
Hint Constructors WfS.


(* Well formed store and frame stack. *)
Inductive WfFS : stenv -> stprops -> store -> stack -> Prop := 
 | WfFS_
   :  forall se sp ss fs
   ,  Forall ClosedT se
   -> StoreM se ss
   -> StoreT se sp ss
   -> StoreP sp fs
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
Hint Resolve wfFS_wfS.


Lemma wfFS_closedT
 :  forall se sp ss fs
 ,  WfFS   se sp ss fs
 -> Forall ClosedT se.
Proof. intros. inverts H. eauto. Qed.
Hint Resolve wfFS_closedT.


Lemma wfFS_typeb
 :  forall se sp ss fs b
 ,  WfFS se sp ss fs
 -> In b ss
 -> (exists t, TypeB nil nil se sp b t).
Proof. 
 intros.
 inverts H. 
 eapply Forall2_exists_left; eauto.
Qed.
Hint Resolve wfFS_typeb.


(* The region handles of private regions are present in the
   store properties. *)
Lemma wfFS_fpriv_sregion
 :  forall se sp ss fs m1 p2
 ,  WfFS se sp ss fs
 -> In (FPriv   m1 p2) fs
 -> In (SRegion p2)    sp.
Proof. intros. inverts H. firstorder. Qed.
Hint Resolve wfFS_fpriv_sregion.


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
 ,  In (SRegion p1) sp
 -> WfFS  se  sp ss fs
 -> WfFS  se  (SRegion p2 <: sp) ss (fs :> FPriv (Some p1) p2).
Proof.
 intros.
 inverts H0. eapply WfFS_; rip.
 unfold StoreP in *. rip.
 - inverts H0; eauto. 
   inverts H4. eauto.
 - inverts H0; eauto.
   inverts H4; eauto.
Qed. 
Hint Resolve wfFS_push_priv_ext.


(* Deallocating a region preserves well-formedness of the store. *)
Lemma typeB_deallocate
 :  forall ke te se sp p b t
 ,  TypeB  ke te se sp b t
 -> TypeB  ke te se sp (deallocRegion p b) t.
Proof.
 intros.
 destruct b.
 - snorm. subst.
   inverts H. eauto.
 - snorm.
Qed.


(* Deallocating bindings preserves the well typedness of the store. *)
Lemma storeT_deallocate
 :  forall se sp ss p
 ,  StoreT se sp ss
 -> StoreT se sp (map (deallocRegion p) ss).
Proof.
 intros.
 unfold StoreT in *.
 eapply Forall2_map_left.
 eapply Forall2_impl.
 - intros.
    eapply typeB_deallocate. eauto. 
 - auto.
Qed.


(* Deallocating top-level region on the top of the frame stack
   preserves the well formedness of the store. *)
Lemma wfFS_region_deallocate
 :  forall se sp ss fs p
 ,  WfFS se sp ss                     (fs :> FPriv None p)
 -> WfFS se sp (map (deallocRegion p) ss) fs.
Proof.
 intros.
 inverts H. eapply WfFS_; rip.
 - unfold StoreM in *.
   rewrite map_length; auto.
 - eapply storeT_deallocate; auto.
 - unfold StoreP in *; snorm; eauto.
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

 - unfold StoreM in *.
   unfold mergeTE. 
   unfold mergeBs.
   repeat (rewrite map_length). auto.

 - unfold StoreT.
   eapply storeT_mergeB; auto.
   
 - eapply storeP_pop; eauto.
Qed.


(* Appending a closed store binding to the store preserves its 
   well formedness. *)
Lemma wfFS_stbind_snoc
 :  forall se sp ss fs p v t
 ,  In (SRegion p) sp
 -> TypeV  nil nil se sp v t
 -> WfFS           se sp ss fs
 -> WfFS   (TRef (TRgn p) t <: se) sp 
           (StValue p v <: ss) fs.
Proof.
 intros.
 inverts H1.
 eapply WfFS_; rip.
 eapply Forall_snoc; eauto.
Qed.


(* Updating bindings preserves the well formedness of the store. *)
Lemma wfFS_stbind_update
 :  forall se sp ss fs l p v t
 ,  get l se = Some (TRef (TRgn p) t)
 -> In (SRegion p) sp
 -> TypeV nil nil se sp v t
 -> WfFS se sp ss fs
 -> WfFS se sp (update l (StValue p v) ss) fs.
Proof.
 intros se sp ss fs l p v t HG HK HV HWF1.
 inverts HWF1. eapply WfFS_; rip.
 - have (length se = length ss).
   unfold StoreM.
   rewritess.
   rewrite update_length. auto.
 - unfold StoreT.
   eapply Forall2_update_right; eauto.
Qed.


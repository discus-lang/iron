
Require Export Iron.Language.SystemF2Effect.Store.Bind.
Require Export Iron.Language.SystemF2Effect.Store.Wf.
Require Export Iron.Language.SystemF2Effect.Store.LiveE.
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Step.FreshF.


(********************************************************************)
Definition LiveBP  (b : stbind) (p : nat) 
 := regionOfStBind b = p -> isStValue b.
Hint Unfold LiveBP.

Definition LiveSP  (ss : store) (p : nat)
 := forall b, In b ss -> LiveBP b p.
Hint Unfold LiveSP.

Inductive  LiveBF : stbind -> frame -> Prop :=
 | LiveBF_FLet
   :  forall b t x
   ,  LiveBF  b (FLet t x)

 | LiveBF_FPrivNone 
   :  forall b p
   ,  LiveBP b p             
   -> LiveBF b (FPriv None p)
 
 | LiveBF_FPrivSome
   :  forall b p1 p2
   ,  LiveBP b p1 -> LiveBP b p2
   -> LiveBF b (FPriv (Some p1) p2).
Hint Constructors LiveBF.

Definition LiveBK  (b : stbind) (fs : stack)
 := forall f, In f fs -> LiveBF b f.

Definition LiveSF  (ss : store) (f : frame)
 := forall b, In b ss -> LiveBF b f.

Definition LiveS (ss : store) (fs : stack)
 := forall b f, In b ss -> In f fs -> LiveBF b f.
Hint Unfold LiveS.


(********************************************************************)
(* Liveness of regions *)
Lemma liveBP_allocRegion
 :  forall se sp b t
 ,  TypeB   nil nil se sp b t
 -> LiveBP  b (allocRegion sp).
Proof.
 unfold LiveBP.
 intros.
 destruct b.
 - eauto.
 - snorm. subst. 
   lets F: allocRegion_fresh sp.
   remember (allocRegion sp) as p.
   inverts H.
   inverts_kind. nope.
Qed.


(********************************************************************)
Lemma liveSP_from_effect
 :  forall e p fs ss
 ,  handleOfEffect e = Some p
 -> LiveE  fs e
 -> LiveS  ss fs
 -> LiveSP ss p.
Proof.
 intros. 
 lets D: liveE_fpriv_in H0 H. clear H0 H.
 unfold LiveS in H1.
 unfold LiveSP. intros.
 destruct D as [m].
 lets D2: H1 H H0.
 inverts D2; auto.
Qed.
Hint Resolve liveSP_from_effect.


(********************************************************************)
Lemma liveBF_stvalue_true
 : forall p v f
 , LiveBF (StValue p v) f.
Proof.
 intros.
 destruct f.
 - auto.
 - destruct o.
   + eapply LiveBF_FPrivSome.
     * unfold LiveBP. eauto.
     * unfold LiveBP. eauto.
   + eapply LiveBF_FPrivNone.
     * unfold LiveBP. eauto.
Qed.
Hint Resolve liveBF_stvalue_true.


(********************************************************************)
Lemma liveSF_store_cons_stvalue
 :  forall ss p v f
 ,  LiveSF ss f
 -> LiveSF (ss :> StValue p v) f.
Proof.
 intros.
 unfold LiveSF in *. 
 intros.
 inverts H0; eauto.
Qed.
Hint Resolve liveSF_store_cons_stvalue.


Lemma liveSF_store_snoc_stvalue
 :  forall ss p v f
 ,  LiveSF ss f
 -> LiveSF (StValue p v <: ss) f.
Proof.
 intros.
 unfold LiveSF in *. 
 intros.
 eapply in_snoc_split in H0.
 inverts H0; eauto.
Qed.
Hint Resolve liveSF_store_cons_stvalue.


Lemma liveSF_store_cons_stdead
 :  forall ss p f
 ,  NoPrivF p f
 -> LiveSF ss f
 -> LiveSF (ss :> StDead p) f.
Proof.
 intros.
 unfold LiveSF in *.
 intros.
 inverts H1; auto.
 destruct f; auto.
 destruct o; auto.
 - eapply LiveBF_FPrivSome.
   + simpl in H. rip.
     unfold LiveBP. intros. 
     snorm. omega.
   + simpl in H. rip.
     unfold LiveBP. intros.
     snorm. omega.
 - eapply LiveBF_FPrivNone.
   + simpl in H. rip.
     unfold LiveBP. intros.
     snorm. omega.
Qed.
Hint Resolve liveSF_store_cons_stdead.


(********************************************************************)
(* Pushing and popping continuation frames. *)

(* Pushing a FLet frame preserves liveness. *)
Lemma liveS_push_flet
 :  forall ss fs t x
 ,  LiveS ss fs
 -> LiveS ss (fs :> FLet t x).
Proof.
 unfold LiveS in *. rip.
 inverts H1; auto.
Qed.


Lemma liveS_push_fpriv_none_allocRegion
 :  forall se sp ss fs 
 ,  WfFS   se sp ss fs 
 -> LiveS  ss fs
 -> LiveS  ss (fs :> FPriv None (allocRegion sp)).
Proof.
 unfold LiveS in *. rip.
 inverts H2; eauto.
 eapply LiveBF_FPrivNone.
 lets D: wfFS_typeb H H1.
 destruct D.
 eapply liveBP_allocRegion. eauto.
Qed.


Lemma liveS_push_fpriv_some_allocRegion
 :  forall se sp ss fs p1
 ,  WfFS   se sp ss fs
 -> LiveSP ss p1
 -> LiveS  ss fs
 -> LiveS  ss (fs :> FPriv (Some p1) (allocRegion sp)).
Proof.
 rip.
 unfold LiveS. intros.
 inverts H3; eauto.
 eapply LiveBF_FPrivSome; eauto.
 lets D: wfFS_typeb H H2.
 destruct D.
 eapply liveBP_allocRegion; eauto.
Qed.


(********************************************************************)
(* Preservation of liveness under store modifications. *)
Lemma liveS_stack_head
 :  forall ss fs f
 ,  LiveS  ss (fs :> f)
 -> LiveSF ss f.
Proof.
 intros.
 unfold LiveS in *.
 unfold LiveSF in *.
 eauto.
Qed.
Hint Resolve liveS_stack_head.


(* Popping a frame preserves liveness. *)
Lemma liveS_stack_tail
 :  forall ss fs f
 ,  LiveS ss (fs :> f)
 -> LiveS ss fs.
Proof.
 intros. 
 unfold LiveS in *. 
 eauto.
Qed.
Hint Resolve liveS_stack_tail.


Lemma liveS_stack_cons
 :  forall ss fs f
 ,  LiveS  ss fs
 -> LiveSF ss f
 -> LiveS  ss (fs :> f).
Proof.
 intros.
 unfold LiveS in *.
 intros.
 inverts H2; eauto.
Qed.
Hint Resolve liveS_stack_cons.


Lemma liveS_store_tail
 :  forall ss b fs
 ,  LiveS (ss :> b) fs
 -> LiveS ss        fs.
Proof.
 intros.
 unfold LiveS in *.
 eauto.
Qed.
Hint Resolve liveS_store_tail.


Lemma liveS_store_head
 :  forall ss b fs
 ,  LiveS  (ss :> b) fs
 -> LiveBK b fs.
Proof.
 intros.
 unfold LiveS in *.
 unfold LiveBK in *.
 firstorder.
Qed.
Hint Resolve liveS_store_head.


Lemma liveS_store_cons
 :  forall b ss fs
 ,  LiveBK b  fs
 -> LiveS  ss fs
 -> LiveS  (ss :> b) fs.
Proof.
 intros.
 unfold LiveS  in *.
 unfold LiveBK in *.
 intros. 
 firstorder. subst. auto.
Qed.
Hint Resolve liveS_store_cons.


Lemma liveS_store_cons_stvalue
 :  forall p v fs ss
 ,  LiveS ss                  fs
 -> LiveS (ss :> StValue p v) fs.
Proof.
 intros.
 induction fs.
 - unfold LiveS in *.
   eauto.
 - have (LiveSF ss a). 
   have (LiveS  ss fs).
   rip.
Qed.
Hint Resolve liveS_store_cons_stvalue.


Lemma liveS_store_snoc_stvalue
 :  forall p v fs ss
 ,  LiveS ss                  fs
 -> LiveS (StValue p v <: ss) fs.
Proof.
 intros.
 induction fs.
 - unfold LiveS in *.
   eauto.
 - have (LiveSF ss a).
   have (LiveS  ss fs).
   rip.
   eapply liveS_stack_cons.
   + eauto.
   + eapply liveSF_store_snoc_stvalue.
     auto.
Qed.
Hint Resolve liveS_store_snoc_stvalue.


Lemma liveS_store_cons_stdead
 :  forall ss p fs
 ,  NoPrivFs p fs
 -> LiveS ss fs
 -> LiveS (ss :> StDead p) fs.
Proof.
 intros.
 induction fs as [| f].
 - eauto.
 - have (LiveS ss fs).
   have (NoPrivFs p fs). rip.
   have (NoPrivF  p f).
   have (LiveSF ss f).
   have (LiveSF (ss :> StDead p) f).
   eapply liveS_stack_cons; auto.
Qed.
Hint Resolve liveS_store_cons_stdead.


Lemma liveS_stvalue_update
 :  forall ss fs l p v
 ,  (exists m, In (FPriv m p) fs)
 -> LiveS  ss fs
 -> LiveS (update l (StValue p v) ss) fs.
Proof.
 intros. gen l.
 induction ss; intros.
 - unfold LiveS.
   destruct l; firstorder. 
 - have (LiveS ss fs). rip.
   destruct l.
   + simpl. 
     eapply liveS_store_cons_stvalue; eauto.
   + simpl.
     have (LiveBK a fs).
     eapply liveS_store_cons; auto.
Qed.


(********************************************************************)
Lemma liveSF_dead_noprivF
 :  forall p ss f
 ,  LiveSF ss f
 -> In (StDead p) ss
 -> NoPrivF p f.
Proof.
 intros.
 unfold LiveSF in *.
 eapply H in H0. clear H.
 inverts H0.
 - snorm.
 - unfold LiveBP in *.
   snorm.
   have (p = p0 \/ ~(p = p0)).
   inverts H0.
   + have (p0 = p0).
     rip.
     unfold isStValue in *. 
     firstorder. nope.
   + auto.
 - unfold LiveBP in *.
   snorm.
   have (p = p1 \/ ~(p = p1)).
   inverts H0; auto.
   + have (p1 = p1).
     rip. unfold isStValue in *.
     firstorder. nope.
   + have (p = p2 \/ ~(p = p2)).
     inverts H0; auto.
     rip. unfold isStValue in *.
     firstorder. nope.
Qed.


Lemma liveS_dead_noprivFs
 :  forall p ss fs
 ,  LiveS ss fs
 -> In (StDead p) ss
 -> NoPrivFs p fs.
Proof.
 intros.
 induction fs as [|f].
 - unfold NoPrivFs in *. auto.
 - have (LiveS  ss fs). rip.
   have (LiveSF ss f).
   eapply Forall_cons.
   + eapply liveSF_dead_noprivF; eauto.
   + auto.
Qed.
Hint Resolve liveS_dead_noprivFs.


Lemma liveS_deallocRegion
 :  forall ss fs p
 ,  NoPrivFs p fs
 -> LiveS ss (fs :> FPriv None p)
 -> LiveS (map (deallocRegion p) ss) fs.
Proof.
 intros.
 induction ss.
 - simpl.
   unfold LiveS in *.
   eauto.
 - destruct a.
   + simpl.
     split_if.
     * snorm. subst.
       eapply liveS_store_tail in H0. rip.
     * have (LiveS ss (fs :> FPriv None p)). 
       rip.
   + simpl.
     have (LiveS ss (fs :> FPriv None p)). 
     rip.
     have (LiveS (ss :> StDead n) fs).
     eapply liveS_store_cons_stdead; auto.
     eapply liveS_dead_noprivFs.
     * eapply H2.
     * eauto.
Qed.


Lemma liveS_liveE_value
 :  forall ss fs e l b p
 ,  LiveS ss fs
 -> LiveE fs e
 -> handleOfEffect e = Some p
 -> get l ss         = Some b
 -> regionOfStBind b = p
 -> exists v, b = StValue p v.
Proof.
 intros ss fs e l b p HLS HLE. intros.

 destruct b.
 - snorm. subst. exists v. eauto.
 - simpl in H1. inverts H1. clear H2.
   have (In (StDead p) ss). clear H0.

   have (NoPrivFs p fs).

   lets D1: liveE_fpriv_in HLE H.
   destruct D1 as [m].

   lets D2: (@Forall_in frame) H0 H2. 
   simpl in D2.
   destruct m; firstorder.
Qed.


Lemma liveS_mergeB
 :  forall ss fs p1 p2
 ,  LiveSP ss p2
 -> LiveS  ss fs
 -> LiveS  (map (mergeB p1 p2) ss) fs. 
Proof.
 intros.
 induction ss as [| b].
 - snorm.
 - have (LiveS  ss fs).
   have (LiveSP ss p2).
   have (LiveBP b  p2).
   rip. simpl.

   eapply liveS_store_cons; auto.
   clear IHss.

   destruct b.
   + Case "StValue".
     snorm.
     * subst.
       firstorder.
     * firstorder.

   + Case "StDead".

     have (n = p2 \/ ~(n = p2)) as HN.
     inverts HN.
     * simpl. snorm.
        unfold LiveBP in H3.
        snorm. unfold isStValue in H3.
        destruct H3. destruct H3. nope.
        nope.
 
     * subst.
       simpl. snorm. nope. firstorder.
Qed.



Require Export Iron.Language.SystemF2Effect.Store.Bind.
Require Export Iron.Language.SystemF2Effect.Store.StoreT.
Require Export Iron.Language.SystemF2Effect.Store.StoreP.
Require Export Iron.Language.SystemF2Effect.Store.LiveE.
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Step.FreshF.


(********************************************************************)
(* All store bindings in regions defined by FPriv frames are live *)
Definition LiveS  (ss : store) (fs : stack)
 := (forall b m
       ,  In b ss -> In (FPriv m (regionOfStBind b))   fs 
       -> isStValue b).
 

(********************************************************************)
(* Pushing and popping continuation frames. *)

(* Pushing a FLet frame preserves liveness. *)
Lemma liveS_push_flet
 :  forall ss fs t x
 ,  LiveS ss fs
 -> LiveS ss (fs :> FLet t x).
Proof.
 unfold LiveS in *.
 intros. snorm.
 inverts H1; nope; eauto.
Qed.


(* Pushing a FPriv frame with a fresh region identifier
   preserves liveness. *)
Lemma liveS_push_fpriv_allocRegion
 :  forall se sp ss fs m 
 ,  STORET se sp ss
 -> STOREP sp fs
 -> LiveS  ss fs
 -> LiveS  ss (fs :> FPriv m (allocRegion sp)).
Proof.
 unfold LiveS in *.
 rip.
 destruct b.
 - eauto.
 - apply H1 with (m := m) in H2. auto.
   unfold regionOfStBind in *.
   snorm.
   inverts H3; auto.
   + inverts H4.
     lets F: allocRegion_fresh sp.
     remember (allocRegion sp) as p.
     
     lets D: storet_handles_in_stprops H.
     have HP: (regionOfStBind (StDead p) = p).
     snorm. eapply D with (p := p) in H2. tauto.
     snorm.
   + eapply H1 in H2.
     * nope.
     * eauto. 
Qed.


(* Popping a frame preserves liveness. *)
Lemma liveS_pop
 :  forall ss fs f
 ,  LiveS ss (fs :> f)
 -> LiveS ss fs.
Proof.
 intros.
 unfold LiveS in *; rip; eauto.
Qed.
Hint Resolve liveS_pop.


(********************************************************************)
(* Preservation of liveness under store modifications. *)

Lemma liveS_stdead_cons
 :  forall ss p fs
 ,   (forall m, ~(In (FPriv m p) fs))
 ->  LiveS ss fs
 ->  LiveS (ss :> StDead p) fs.
Proof.
 intros.
 unfold LiveS in *; rip.
 inverts H1; firstorder.
Qed.
Hint Resolve liveS_stdead_cons.


Lemma liveS_stvalue_cons
 :  forall p v fs ss
 ,  LiveS ss                  fs
 -> LiveS (ss :> StValue p v) fs.
Proof.
 intros. 
 unfold LiveS in *.
 intros.
 destruct b.
 - eauto. 
 - firstorder. nope.
Qed.


Lemma liveS_stvalue_snoc
 :  forall p v fs ss
 ,  LiveS ss                  fs
 -> LiveS (StValue p v <: ss) fs.
Proof.
 intros.
 unfold LiveS in *.
 intros.
 destruct b.
 - eauto.
 - rrwrite (  StValue p v <: ss 
           = (StValue p v <: nil) >< ss).
   eapply in_app_split in H0.
   inverts H0. 
   + firstorder.
   + firstorder. nope.
Qed.


Lemma liveS_store_tail
 :  forall ss s fs
 ,  LiveS (ss :> s) fs
 -> LiveS ss        fs.
Proof.
 intros.
 unfold LiveS in *. 
 firstorder.
Qed.
Hint Resolve liveS_store_tail.


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
     eapply liveS_stvalue_cons; eauto.
   + simpl. firstorder.
Qed.


Lemma liveS_deallocate
 :  forall ss fs p
 ,  (forall m, ~(In (FPriv m p) fs))
 -> LiveS ss (fs :> FPriv None p)
 -> LiveS (map (deallocate p) ss) fs.
Proof.
 intros.
 induction ss.
 - firstorder. 
 - destruct a.
   + simpl.
     split_if.
     * snorm. subst.
       eapply liveS_store_tail in H0. rip.

     * have (LiveS ss (fs :> FPriv None p)). 
       firstorder.
   + firstorder.
Qed.


(********************************************************************)
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
 - lets D: liveE_fpriv_in HLE H.
   destruct D as [m]. eauto.

   snorm. subst.
   have (In (StDead p) ss) as HD.
   unfold LiveS in *. 
   eapply HLS in HD.
   + unfold isStValue in HD. nope.
   + eauto. 
Qed.


Lemma liveS_dead_nopriv
 :  forall m p ss fs
 ,  In (StDead p) ss
 -> LiveS ss fs
 -> ~(In (FPriv m p) fs).
Proof.
 intros.
 unfold not. intros.
 unfold LiveS in *.
 eapply H0 in H.
 unfold isStValue in H. 
  firstorder. nope.
  eauto.
Qed.


Lemma liveS_mergeB
 :  forall ss fs p1 p2
 ,  LiveS ss fs
 -> LiveS (map (mergeB p1 p2) ss) fs. 
Proof.
 intros.
 induction ss.
 - snorm.
 - destruct a.
   + Case "StValue".
     snorm.
     * subst.
       eapply liveS_stvalue_cons.
       firstorder.
     * firstorder.
   + Case "StDead".
     snorm.
     eapply liveS_stdead_cons.
     * intros.
       eapply liveS_dead_nopriv in H; eauto.
     * firstorder.
Qed.
  

 

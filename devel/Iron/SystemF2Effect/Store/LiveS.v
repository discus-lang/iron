
Require Export Iron.SystemF2Effect.Step.Frame.
Require Export Iron.SystemF2Effect.Store.Bind.
Require Export Iron.SystemF2Effect.Store.TypeS.
Require Export Iron.SystemF2Effect.Store.StoreP.
Require Export Iron.SystemF2Effect.Store.LiveE.


Definition LiveS  (ss : store) (fs : stack)
 :=  forall b
  ,  In b ss
  -> In (FUse (regionOfStBind b)) fs
  -> isStValue b. 


Lemma liveS_push_fLet
 :  forall ss fs t x
 ,  LiveS ss fs
 -> LiveS ss (fs :> FLet t x).
Proof.
 intros.
 unfold LiveS in *.
 intros.
 snorm.
 inverts H1.
 - nope.
 - eauto.
Qed.


Lemma liveS_pop_fLet
 :  forall ss fs t x
 ,  LiveS ss (fs :> FLet t x)
 -> LiveS ss fs.
Proof.
 intros.
 unfold LiveS in *.
 snorm.
Qed.


(********************************************************************)
Lemma liveS_push_fUse_fresh
 :  forall se sp ss fs 
 ,  STORET se sp ss
 -> STOREP sp fs
 -> LiveS  ss fs
 -> LiveS  ss (fs :> FUse (allocRegion sp)).
Proof.
 unfold LiveS in *.
 intros.
 destruct b.
 - unfold isStValue. eauto.
 - apply H1 in H2. auto. clear H1.
   unfold regionOfStBind in *.
   snorm.
   inverts H3. 
   + inverts H1.
     lets F: allocRegion_fresh sp.
     remember (allocRegion sp) as p.
     
     lets D: storet_handles_in_stprops H.
     have HP: (regionOfStBind (StDead p) = p).
     snorm. eapply D with (p := p) in H2. tauto.
     snorm.
   + auto.
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
 - snorm. subst.
   have (In (StDead p) ss) as HD.
   unfold LiveS in *. 
   eapply HLS in HD.
   + unfold isStValue in HD. nope.
   + snorm.
     eapply liveE_fUse_in; eauto.
Qed.


(********************************************************************)
Lemma liveS_deallocate
 :  forall ss fs p
 ,  ~(In (FUse p) fs)
 -> LiveS ss (fs :> FUse p)
 -> LiveS (deallocate p ss) fs.
Proof.
 intros.
 induction ss.
 - admit. 
 - destruct a.
   + simpl.
     split_if.
     * snorm. subst.
       admit. (* need LiveS_cons and LiveS_cons_dead *)

     * snorm.
       have (LiveS ss (fs :> FUse p)) by admit. rip.
       unfold LiveS in IHss.
       unfold LiveS. intros. snorm.
       inverts H2.
        eauto.
        eapply IHss; auto.

   + simpl.
     have (LiveS ss (fs :> FUse p)) by admit. rip.
     admit. (* need LiveS_cons *)
Qed.


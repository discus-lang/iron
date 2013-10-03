
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.Bind.
Require Export Iron.Language.SystemF2Effect.Store.StoreT.
Require Export Iron.Language.SystemF2Effect.Store.StoreP.
Require Export Iron.Language.SystemF2Effect.Store.LiveE.


(********************************************************************)
Definition LiveS  (ss : store) (fs : stack)
 :=  forall b
  ,  In b ss
  -> In (FUse (regionOfStBind b)) fs
  -> isStValue b. 


(********************************************************************)
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


Lemma liveS_store_tail
 :  forall ss s fs
 ,  LiveS (ss :> s) fs
 -> LiveS ss        fs.
Proof.
 intros.
 unfold LiveS in *.
 snorm.
Qed.
Hint Resolve liveS_store_tail.


Lemma liveS_stack_tail
 :  forall ss fs f
 ,  LiveS ss (fs :> f)
 -> LiveS ss fs.
Proof.
 intros.
 unfold LiveS in *.
 snorm.
Qed.
Hint Resolve liveS_stack_tail.


Lemma liveS_stdead_cons
 :  forall ss p fs
 ,  ~(In (FUse p) fs)
 ->  LiveS ss fs
 ->  LiveS (ss :> StDead p) fs.
Proof.
 intros.
 unfold LiveS in *.
 snorm.
 inverts H1.
 - unfold regionOfStBind in H2. tauto.
 - eauto.
Qed.
Hint Resolve liveS_stdead_cons.


Lemma liveS_stvalue_cons
 :  forall p v fs ss
 ,  In (FUse p) fs
 -> LiveS ss                  fs
 -> LiveS (ss :> StValue p v) fs.
Proof.
 intros.
 unfold LiveS in *.
 snorm.
 inverts H1; eauto.
Qed.


Lemma liveS_stvalue_snoc
 :  forall p v fs ss
 ,  In (FUse p) fs
 -> LiveS ss                  fs
 -> LiveS (StValue p v <: ss) fs.
Proof.
 intros.
 unfold LiveS in *.
 snorm.
 rrwrite ( StValue p v <: ss 
         = (nil :> StValue p v) >< ss) in H1.
 eapply in_app_split in H1.
 inverts H1.
 - eauto.
 - eauto.
   simpl in H3. inverts H3.
   unfold isStValue. eauto. nope.
Qed.


Lemma liveS_stvalue_update
 :  forall ss fs l p v
 ,  In (FUse p) fs
 -> LiveS  ss fs
 -> LiveS (update l (StValue p v) ss) fs.
Proof.
 intros. gen l.
 induction ss; intros.
 - unfold LiveS.
   intros.
   destruct l; snorm.
 - have (LiveS ss fs). rip.
   destruct l.
   + simpl. 
     eapply liveS_stvalue_cons; eauto.
   + simpl.
     unfold LiveS in *. snorm.
     inverts H2. eauto. eauto.
Qed.


Lemma liveS_deallocate
 :  forall ss fs p
 ,  ~(In (FUse p) fs)
 -> LiveS ss (fs :> FUse p)
 -> LiveS (map (deallocate p) ss) fs.
Proof.
 intros.
 induction ss.
 - unfold LiveS. snorm.
 - destruct a.
   + simpl.
     split_if.
     * snorm. subst.
       eapply liveS_store_tail in H0. rip.

     * snorm.
       have (LiveS ss (fs :> FUse p)). rip.
       unfold LiveS in IHss.
       unfold LiveS. intros. snorm.
       inverts H2.
        eauto.
        eapply IHss; auto.

   + simpl.
     have (LiveS ss (fs :> FUse p)). rip.
     have (LiveS (ss :> StDead n) fs).
     clear H H0 H1.
     unfold LiveS in *.
     snorm.
     inverts H.
     * lets D: H2 (StDead n).
       eapply D. eauto. auto.
     * eauto.
Qed.
   

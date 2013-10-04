
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(* All region handles on frame stack are in store properties.

   We don't require the other way, forcing all store properties to be in 
   the frame stack. This is because we need to be able to pop a Use frame and
   still have any region handles in the expression being well typed, along with
   dangling references into that region. *)

Definition STOREP  (sp : stprops) (fs : stack)
 := (forall p,     In (FPriv p)    fs -> In (SRegion p)  sp)
 /\ (forall p1 p2, In (FExt p1 p2) fs -> In (SRegion p1) sp)
 /\ (forall p1 p2, In (FExt p1 p2) fs -> In (SRegion p2) sp).


(* Weaken frame stack in store properties. *)
Lemma storep_snoc
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (SRegion p <: sp) (fs :> FPriv p).
Proof.
 unfold STOREP in *. rip.

 - have HN: (p0 = p \/ ~(p0 = p)).
   inverts HN.
   + rrwrite (SRegion p <: sp = (SRegion p <: nil) >< sp).
     snorm.
   + assert (In (FPriv p0) fs).
      eapply in_tail.
      have (FPriv p0 <> FPriv p) by congruence.
      eauto. auto.
     rrwrite (SRegion p <: sp = (SRegion p <: nil) >< sp).
     snorm.

 - have HN: (p1 = p \/ ~(p1 = p)).
   inverts HN.
   + rrwrite (SRegion p <: sp = (SRegion p <: nil) >< sp).
     snorm.
   + assert (In (FExt p1 p2) fs).
      eapply in_tail.
      have (FExt p1 p2 <> FPriv p) by congruence. 
      eauto. auto.
     rrwrite (SRegion p <: sp = (SRegion p <: nil) >< sp).
     snorm. eauto.

 - have HN: (p2 = p \/ ~(p2 = p)).
   inverts HN.
   + rrwrite (SRegion p <: sp = (SRegion p <: nil) >< sp).
     snorm.
   + assert (In (FExt p1 p2) fs).
      eapply in_tail.
      have (FExt p1 p2 <> FPriv p) by congruence. 
      eauto. auto.
     rrwrite (SRegion p <: sp = (SRegion p <: nil) >< sp).
     snorm. eauto.
Qed.
Hint Resolve storep_snoc.


Lemma storep_stprops_snoc
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (p <: sp) fs.
Proof.
 unfold STOREP in *. rip.
 - have (In (SRegion p1) sp). snorm.
 - have (In (SRegion p2) sp). snorm.
Qed.
Hint Resolve storep_stprops_snoc.


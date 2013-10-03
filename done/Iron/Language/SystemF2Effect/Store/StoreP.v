
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(* All region handles on frame stack are in store properties.

   We don't require the other way, forcing all store properties to be in 
   the frame stack. This is because we need to be able to pop a Use frame and
   still have any region handles in the expression being well typed, along with
   dangling references into that region. *)

Definition STOREP  (sp : stprops) (fs : stack)
 := forall n, In (FPriv n) fs -> In (SRegion n) sp.


(* Weaken frame stack in store properties. *)
Lemma storep_snoc
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (SRegion p <: sp) (fs :> FPriv p).
Proof.
 unfold STOREP in *.
 - intros.
   have HN: (n = p \/ ~(n = p)).
   inverts HN.
   + rrwrite (  SRegion p <: sp 
             = (SRegion p <: nil) >< sp).
     snorm.
   + assert (In (FPriv n) fs).
      eapply in_tail.
      have (FPriv n <> FPriv p) by congruence.
      eauto. auto.
     rrwrite (  SRegion p <: sp
             = (SRegion p <: nil) >< sp).
     snorm.
Qed.
Hint Resolve storep_snoc.


Lemma storep_stprops_snoc
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (p <: sp) fs.
Proof.
 unfold STOREP in *.
 snorm.
Qed.
Hint Resolve storep_stprops_snoc.

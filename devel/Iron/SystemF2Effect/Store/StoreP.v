
Require Export Iron.SystemF2Effect.Step.Frame.
Require Export Iron.SystemF2Effect.Store.Bind.


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


Lemma storep_stprops_cons
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (sp :> p) fs.
Proof.
 unfold STOREP in *.
 snorm.
Qed.
Hint Resolve storep_stprops_cons.


Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(* All region identifiers for private regions defined in the frame
   stack are in the store properties.

   We don't require the other way, forcing all store properties to be in 
   the frame stack. This is because we need to be able to pop a Priv frame
   and still have any region handles in the expression being well typed,
   along with dangling references into that region. *)
Definition STOREP  (sp : stprops) (fs : stack)
 := (forall m1 p2, In (FPriv  m1       p2) fs -> In (SRegion p2) sp)
 /\ (forall p1 p2, In (FPriv (Some p1) p2) fs -> In (SRegion p1) sp).


(* Weaken frame stack in store properties. *)
Lemma storep_snoc
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (SRegion p <: sp) (fs :> FPriv None p).
Proof.
 unfold STOREP in *. rip.
 - inverts H0. inverts H.
   + eauto.
   + have HN: (p = p2 \/ ~(p = p2)).
     inverts HN; eauto.
 - inverts H0; nope; eauto.
Qed.
Hint Resolve storep_snoc.


Lemma storep_stprops_snoc
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (p <: sp) fs.
Proof.
 unfold STOREP in *. rip; eauto.
Qed.
Hint Resolve storep_stprops_snoc.


Lemma storep_pop
 :  forall sp fs f
 ,  STOREP sp (fs :> f)
 -> STOREP sp fs.
Proof.
 intros.
 unfold STOREP in *.
 firstorder.
Qed.
Hint Resolve storep_pop.

Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(* All region identifiers for private regions defined in the frame
   stack are in the store properties.

   We don't require the other way, forcing all store properties to be in 
   the frame stack. This is because we need to be able to pop a Priv frame
   and still have any region handles in the expression being well typed,
   along with dangling references into that region. *)
Definition StoreP  (sp : stprops) (fs : stack)
 := (forall m1 p2, In (FPriv  m1       p2) fs -> In (SRegion p2) sp)
 /\ (forall p1 p2, In (FPriv (Some p1) p2) fs -> In (SRegion p1) sp).


(* Weaken frame stack in store properties. *)
Lemma storeP_snoc
 :  forall sp fs p
 ,  StoreP sp fs
 -> StoreP (SRegion p <: sp) (fs :> FPriv None p).
Proof.
 unfold StoreP in *. rip.
 - inverts H0. inverts H.
   + eauto.
   + have HN: (p = p2 \/ ~(p = p2)).
     inverts HN; eauto.
 - inverts H0; nope; eauto.
Qed.
Hint Resolve storeP_snoc.


Lemma storeP_stprops_snoc
 :  forall sp fs p
 ,  StoreP sp fs
 -> StoreP (p <: sp) fs.
Proof.
 unfold StoreP in *. rip; eauto.
Qed.
Hint Resolve storeP_stprops_snoc.


Lemma storeP_pop
 :  forall sp fs f
 ,  StoreP sp (fs :> f)
 -> StoreP sp fs.
Proof.
 intros.
 unfold StoreP in *.
 firstorder.
Qed.
Hint Resolve storeP_pop.

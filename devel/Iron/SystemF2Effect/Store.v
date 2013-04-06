
Require Export Iron.SystemF2Effect.Store.Wf.
Require Export Iron.SystemF2Effect.Store.TypeB.
Require Export Iron.SystemF2Effect.Store.TypeS.


(* Reading bindings **********************************************************)
(* Values read from the store have the types predicted by
   the store environment *)
Lemma storet_get_typev
 :  forall se sp ss ix r v t
 ,  STORET se sp ss
 -> get ix se = Some (TRef (TCap (TyCapRegion r)) t)
 -> get ix ss = Some (StValue r v)
 -> TYPEV nil nil se sp v t.
Proof.
 intros.
 unfold STORET in *.
 lets D: (@Forall2_get_get_same stbind ty) H1 H0. eauto.
 inverts D. auto.
Qed.


(* Updating bindings *********************************************************)
(* Store with an updated binding is still well formed. *)
Lemma store_update_wffs
 :  forall se sp ss fs l r v t
 ,  WfFS se sp ss fs
 -> get l se = Some (TRef (TCap (TyCapRegion r)) t)
 -> KindT nil sp (TCap (TyCapRegion r)) KRegion
 -> TYPEV nil nil se sp v t
 -> WfFS se sp (update l (StValue r v) ss) fs.
Proof.
 intros se sp ss fs l r v t HWF1 HG HV.
 inverts HWF1. rip.
 - have (length se = length ss).
   unfold STOREM.
   rewritess.
   rewrite update_length. auto.
 - unfold STORET.
   eapply Forall2_update_right; eauto.
Qed.



Require Export Iron.SystemF2Effect.Step.Frame.
Require Export Iron.SystemF2Effect.Store.Bind.


(* All region handles in this effect have corresponding 
   FUse frames in the frame stack. *)
Definition LiveE (fs : stack) (e : ty)
 := forall p
   ,  (In (TRead  (TCap (TyCapRegion p))) (flattenT e) -> In (FUse p) fs)
   /\ (In (TWrite (TCap (TyCapRegion p))) (flattenT e) -> In (FUse p) fs)
   /\ (In (TAlloc (TCap (TyCapRegion p))) (flattenT e) -> In (FUse p) fs).
Global Opaque LiveE.


Lemma liveE_subsT
 :  forall ke sp e1 e2 fs
 ,  SubsT ke sp e1 e2 KEffect
 -> LiveE fs e1 
 -> LiveE fs e2.
Proof.
 admit.       (* TODO: liveE_subsT *)
Qed.
Hint Resolve liveE_subsT.


Lemma liveE_sum_above
 :  forall e1 e2 fs
 ,  LiveE  fs e1 -> LiveE fs e2 
 -> LiveE  fs (TSum e1 e2).
Proof.
 admit.       (* TODO: liveE_sum_above. *)
Qed.
Hint Resolve liveE_sum_above.


Lemma liveE_frame_cons
 :  forall fs f e
 ,  LiveE  fs        e
 -> LiveE  (fs :> f) e.
Proof.
 admit.       (* TODO: liveE_frame_cons *)
Qed.
Hint Resolve liveE_frame_cons.


Lemma liveE_pop_flet
 :  forall fs t x e
 ,  LiveE  (fs :> FLet t x) e
 -> LiveE  fs e.
Proof.
 admit.       (* TODO: liveE_pop_flet *)
Qed.


Lemma liveE_maskOnVarT
 :  forall fs e n
 ,  LiveE  fs (maskOnVarT n e)
 -> LiveE  fs e.
Proof.
 admit.       (* TODO: liveE_maskOnVarT *)
Qed.


Lemma liveE_phase_change
 :  forall fs p e
 ,  LiveE (fs :> FUse p) e
 -> LiveE (fs :> FUse p) (substTT 0 (TCap (TyCapRegion p)) e).
Proof.
 admit.       (* TODO: liveE_phase_change *)
Qed.


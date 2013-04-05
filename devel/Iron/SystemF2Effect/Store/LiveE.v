
Require Export Iron.SystemF2Effect.Step.Frame.
Require Export Iron.SystemF2Effect.Store.Bind.


Fixpoint handleOfEffect (e : ty) : option nat
 := match e with
    | TCap (TyCapRegion p) => Some p
    | _                    => None
    end.


(* All region handles in this effect have corresponding 
   FUse frames in the frame stack. *)
Definition LiveEs (fs : stack) (es : list ty)
 := Forall (fun e1 => forall p, handleOfEffect e1 = Some p
                   -> In (FUse p) fs)
           es.


Definition LiveE  (fs : stack) (e : ty)
 := LiveEs fs (flattenT e).


(*******************************************************************)
Lemma liveEs_equivTs
 :  forall  ke sp es1 es2 fs
 ,  EquivTs ke sp es1 es2 KEffect
 -> LiveEs  fs es1
 -> LiveEs  fs es2.
Proof.
 intros.
 inverts H.
 unfold LiveEs in *.
 snorm.
 apply  H4 in H. 
 eapply H0 in H; eauto.
Qed.


Lemma liveE_equivT
 :  forall ke sp e1 e2 fs 
 ,  EquivT ke sp e1 e2 KEffect
 -> LiveE  fs e1
 -> LiveE  fs e2.
Proof.
 intros.
 unfold LiveE in *.
 eapply liveEs_equivTs.
  eapply equivT_equivTs; eauto.
  auto.
Qed.


(*******************************************************************)
Lemma liveEs_subsTs
 :  forall ke sp es1 es2 fs
 ,  SubsTs ke sp es1 es2 KEffect
 -> LiveEs fs es1
 -> LiveEs fs es2.
Proof.
 intros.
 inverts H.
 unfold LiveEs in *.
 snorm. 
 eapply H0; eauto.
Qed.


Lemma liveE_subsT
 :  forall ke sp e1 e2 fs
 ,  SubsT ke sp e1 e2 KEffect
 -> LiveE fs e1 
 -> LiveE fs e2.
Proof.
 intros.
 unfold LiveE in *.
 eapply liveEs_subsTs.
  eapply subsT_subsTs in H; eauto.
  auto.
Qed.
Hint Resolve liveE_subsT.


(********************************************************************)
Lemma liveE_sum_above
 :  forall e1 e2 fs
 ,  LiveE  fs e1 -> LiveE fs e2 
 -> LiveE  fs (TSum e1 e2).
Proof.
 intros.
 unfold LiveE. simpl.
 unfold LiveEs.
 eapply Forall_app; eauto.
Qed.
Hint Resolve liveE_sum_above.


Lemma liveE_frame_cons
 :  forall fs f e
 ,  LiveE  fs        e
 -> LiveE  (fs :> f) e.
Proof.
 intros.
 unfold LiveE in *.
 unfold LiveEs in *.
 snorm. 
 right. eauto.
Qed.
Hint Resolve liveE_frame_cons.


Lemma liveE_pop_flet
 :  forall fs t x e
 ,  LiveE  (fs :> FLet t x) e
 -> LiveE  fs e.
Proof.
 intros.
 unfold LiveE in *.
 unfold LiveEs in *.
 snorm.
 spec H x0. rip.
 spec H p.  rip.
 inverts H.
  nope.
  auto.
Qed.


Lemma liveE_maskOnVarT
 :  forall fs e n
 ,  LiveE  fs (maskOnVarT n e)
 -> LiveE  fs e.
Proof.
 intros.
 unfold LiveE in *.
 unfold LiveEs in *.
 snorm.
  admit.      (* ok, effect is on handle, so not masked. *)
Qed.


Lemma liveE_phase_change
 :  forall fs p e
 ,  LiveE (fs :> FUse p) e
 -> LiveE (fs :> FUse p) (substTT 0 (TCap (TyCapRegion p)) e).
Proof.
 admit.       (* TODO: liveE_phase_change *)
Qed.


Global Opaque LiveE.



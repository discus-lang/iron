
Require Export Iron.Language.SystemF2Cap.Step.Frame.
Require Export Iron.Language.SystemF2Cap.Store.Bind.


(********************************************************************)
(* All region handles in this effect have corresponding 
   FUse frames in the frame stack. *)

(* Atomic effect is live relative to the frame stack, which means
   there is a frame which defines the target region. *)
Definition LiveE1_stack (fs : stack) (e : ty)
 :=  forall p2
  ,  handleOfEffect e = Some p2
  -> (exists m1 ts, In (FPriv m1 p2 ts) fs).

Definition LiveEs (fs : stack) (es : list ty)
 := Forall (fun e1 => LiveE1_stack fs e1) es.

Definition LiveE  (fs : stack) (e : ty)
 := LiveEs fs (flattenT e).


(*******************************************************************)
Lemma liveEs_equivTs
 :  forall  ke sp es1 es2 fs
 ,  EquivTs ke sp es1 es2 KEffect
 -> LiveEs  fs es1
 -> LiveEs  fs es2.
Proof.
 intros. inverts H.
 unfold LiveEs in *.
 snorm.
Qed.


Lemma liveE_equivT_left
 :  forall ke sp e1 e2 fs
 ,  EquivT ke sp e1 e2 KEffect 
 -> LiveE  fs e2
 -> LiveE  fs e1.
Proof.
 intros.
 unfold LiveE in *.
 eapply liveEs_equivTs.
 - eapply equivT_equivTs; auto.
   eapply EqSym.
   + eauto.
   + have (KindT ke sp e2 KEffect).
     eauto.
   + auto.
 - auto.
Qed.


Lemma liveE_equivT_right
 :  forall ke sp e1 e2 fs 
 ,  EquivT ke sp e1 e2 KEffect
 -> LiveE  fs e1
 -> LiveE  fs e2.
Proof.
 intros.
 unfold LiveE in *.
 eapply liveEs_equivTs.
 - eapply equivT_equivTs; eauto.
 - auto.
Qed.


(*******************************************************************)
Lemma liveEs_subsTs
 :  forall ke sp es1 es2 fs
 ,  SubsTs ke sp es1 es2 KEffect
 -> LiveEs fs es1
 -> LiveEs fs es2.
Proof.
 intros. inverts H.
 unfold LiveEs in *.
 snorm. 
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
 - eapply subsT_subsTs in H; eauto.
 - auto.
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


Lemma liveE_sum_above_left
 :  forall fs e1 e2
 ,  LiveE fs (TSum e1 e2)
 -> LiveE fs e1.
Proof.
 intros.
 unfold LiveE  in *. 
 unfold LiveEs in *.
 snorm.
Qed.
Hint Resolve liveE_sum_above_left.


Lemma liveE_sum_above_right
 :  forall fs e1 e2
 ,  LiveE fs (TSum e1 e2)
 -> LiveE fs e2.
Proof.
 intros.
 unfold LiveE  in *.
 unfold LiveEs in *.
 snorm. 
Qed.


(********************************************************************)
Lemma liveE_frame_cons
 :  forall fs f e
 ,  LiveE  fs        e
 -> LiveE  (fs :> f) e.
Proof.
 intros.
 unfold LiveE in *.
 unfold LiveEs in *.
 snorm.
 have  (LiveE1_stack fs x). clear H.
 unfold LiveE1_stack in *.
 intros.
 lets D: H1 H.
 shift m1. shift ts.
 firstorder.
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
 unfold LiveE1_stack in *.
 spec H x0. rip.
 spec H p2. rip.
 firstorder. nope.
Qed.


Lemma liveE_maskOnVarT
 :  forall fs e n
 ,  LiveE  fs (maskOnVarT n e)
 -> LiveE  fs e.
Proof.
 intros.
 unfold LiveE  in *.
 unfold LiveEs in *.
 unfold LiveE1_stack in *.
 snorm.
 spec H x.
 apply handleOfEffect_form_some in H1.
 destruct H1 as [tc]. rip.
 eapply maskOnVar_effect_remains in H0.
 - eapply H in H0; eauto.
   snorm. nope.
 - eauto.
Qed.


Lemma liveE_phase_change
 :  forall fs m1 p ts e
 ,  LiveE (fs :> FPriv m1 p ts) e
 -> LiveE (fs :> FPriv m1 p ts) (substTT 0 (TRgn p) e).
Proof.
 intros.
 induction e; snorm;
  try (solve [unfold LiveE        in *;
              unfold LiveEs       in *;
              unfold LiveE1_stack in *;
              snorm; inverts H0; nope]).

 - Case "TSum".
   eapply liveE_sum_above.
   + eapply liveE_sum_above_left  in H; eauto.
   + eapply liveE_sum_above_right in H; eauto.

 - Case "TCon1".
   destruct e;
    unfold LiveE; unfold LiveEs; unfold LiveE1_stack; snorm;
    try (solve [inverts H0; snorm; nope]).
   exists m1.
   inverts H0.
   + exists ts. snorm.
   + nope.
Qed.


Lemma liveE_fpriv_in
 :  forall e p2 fs
 ,  LiveE fs e
 -> handleOfEffect e = Some p2
 -> (exists m1 ts, In (FPriv m1 p2 ts) fs).
Proof.
 intros.
 unfold LiveE  in *.
 unfold LiveEs in *.
 snorm.
 eapply handleOfEffect_form_some in H0.
 destruct H0 as [tc]. rip. 
 snorm. 
 lets D: H (TCon1 tc (TRgn p2)). clear H.
 eapply D. snorm. snorm. nope. 
Qed.


Global Opaque LiveE.


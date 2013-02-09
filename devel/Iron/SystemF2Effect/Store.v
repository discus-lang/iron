
Require Import Iron.SystemF2Effect.Kind.
Require Import Iron.SystemF2Effect.Type.KiJudge.
Require Import Iron.SystemF2Effect.Type.Exp.
Require Import Iron.SystemF2Effect.Type.Predicate.Wf.
Require Import Iron.SystemF2Effect.Value.TyJudge.
Require Import Iron.SystemF2Effect.Value.TyJudge.TypeKind.
Require Import Iron.SystemF2Effect.Value.TyJudge.WeakStEnv.
Require Import Iron.SystemF2Effect.Value.Exp.
Require Export Iron.SystemF2Effect.Store.Bind.
Require Export Iron.SystemF2Effect.Step.Frame.


(* Store typing models the store.
   All types in the store typing have a corresponding binding in
   the store *)
Definition STOREM (se: stenv) (ss: store)
 := length se = length ss.
Hint Unfold STOREM.


(* Well typed store. *)
Definition STORET (se: stenv) (sp: stprops) (ss: store)
 := Forall2 (TYPEB nil nil se sp) ss se.
Hint Unfold STORET.


(* Store properties model use frames on stack. *)
Definition STOREP  (sp : stprops) (fs : stack)
 := forall n, In (SRegion n) sp <-> In (FUse n) fs.


(******************************************************************************)
(* Well formed store. *)
Definition WfS  (se: stenv) (sp: stprops)  (ss: store)
 := Forall closedT se
 /\ STOREM se    ss
 /\ STORET se sp ss.
Hint Unfold WfS.


(* Well formed store and frame stack. *)
Definition WfFS (se : stenv) (sp : stprops) (ss : store) (fs : stack) 
 := Forall closedT se
 /\ STOREM se ss
 /\ STORET se sp ss
 /\ STOREP sp fs.


Lemma wfFS_wfS 
 :  forall se sp ss fs
 ,  WfFS   se sp ss fs
 -> WfS    se sp ss.
Proof. firstorder. Qed.


Lemma storep_cons
 :  forall sp fs p
 ,  STOREP sp fs
 -> STOREP (sp :> SRegion p) (fs :> FUse p).
Proof.
 unfold STOREP in *.
 intros. split.
 - intros.
   have HN: (n = p \/ ~(n = p)).
   inverts HN.
   + simpl. auto.
   + assert (In (FUse n) fs).
      eapply H.
      eapply in_tail. 
      have (SRegion n <> SRegion p) by congruence.
      eauto. eauto. 
     eapply in_split; burn.

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


Lemma storet_weak_stprops
 :  forall se sp ss p
 ,  STORET se sp ss
 -> STORET se (sp :> SRegion p) ss.
Proof.
 intros.
 unfold STORET in *.
 eapply Forall2_impl.
  intros. eapply typeb_stprops_cons. eauto.
 auto.
Qed.
Hint Resolve storet_weak_stprops.


Lemma wffs_sregion_cons
 :  forall se sp ss fs p
 ,  WfFS se sp ss fs
 -> WfFS se (sp :> SRegion p) ss (fs :> FUse p).
Proof. 
 intros.
 unfold WfFS. 
 inverts H. inverts H1. inverts H2.
 auto.
Qed.
Hint Resolve wffs_sregion_cons.


(* Extending the store ********************************************************)
(* Extended store environment models the extended store *)
Lemma storem_snoc
 :  forall se ss t stv
 ,  STOREM se ss
 -> STOREM (t <: se) (stv <: ss).
Proof.
 intros.
 unfold STOREM.
 have (length se = length ss). 
 burn.
Qed.
Hint Resolve storem_snoc.


(* Extended store is well typed under extended store environment *)
Lemma storet_snoc
 :  forall se sp ss r1 v1 t2
 ,  TYPEV  nil nil se sp v1 t2
 -> STORET                                     se  sp                   ss
 -> STORET (tRef (TCap (TyCapRegion r1)) t2 <: se) sp (StValue r1 v1 <: ss).
Proof.
 intros.
 set (tRef' := tRef (TCap (TyCapRegion r1)) t2).

 assert (TYPEB nil nil (tRef' <: se) sp (StValue r1 v1) tRef').
  apply TbValue.
   apply typev_stenv_snoc.
    subst tRef'.
    assert (closedT t2).
     unfold closedT.
     rrwrite (0 = @length ki nil).
     apply (kind_wfT nil sp t2 KData).

     (* NOTE: This one has to be done manually to instantiate existentials *)
     apply (typex_kind_type nil nil se sp (XVal v1) t2 (TBot KEffect)).
    auto. auto. auto.
     
 assert (Forall2 (TYPEB nil nil (tRef' <: se) sp) ss se).
  lets D: (@Forall2_impl stbind ty) 
                (TYPEB nil nil se sp) 
                (TYPEB nil nil (tRef' <: se) sp)
                ss se H0.
  intros.
  apply typeb_stenv_snoc.
   auto.
   subst tRef'. eauto.
  auto. auto.
Qed.
Hint Resolve storet_snoc.


(* Reading bindings ***********************************************************)
(* Values read from the store have the types predicted by
   the store environment *)
Lemma storet_get_typev
 :  forall se sp ss ix r v t
 ,  STORET se sp ss
 -> get ix se = Some (tRef (TCap (TyCapRegion r)) t)
 -> get ix ss = Some (StValue r v)
 -> TYPEV nil nil se sp v t.
Proof.
 intros.
 unfold STORET in *.
 lets D: (@Forall2_get_get_same stbind ty) H1 H0. eauto.
 inverts D. auto.
Qed.


(* Updating bindings **********************************************************)
(* Store with an updated binding is still well formed. *)
Lemma store_update_wf
 :  forall se sp ss l r v t
 ,  WfS se sp ss
 -> get l se = Some (tRef (TCap (TyCapRegion r)) t)
 -> TYPEV nil nil se sp v t
 -> WfS se sp (update l (StValue r v) ss).
Proof.
 intros se sp ss l r v t HWF1 HG HV.
 inverts HWF1. rip.
  have (length se = length ss).
   unfold STOREM.
   rewritess.
   rewrite update_length. auto.
  unfold STORET.
   eapply Forall2_update_right; eauto.
Qed.

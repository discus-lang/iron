
Require Import Iron.Language.SystemF2Effect.Theory.SubstTypeExp.
Require Import Iron.Language.SystemF2Effect.Theory.SubstValExp.
Require Import Iron.Language.SystemF2Effect.Kind.
Require Import Iron.Language.SystemF2Effect.Type.
Require Import Iron.Language.SystemF2Effect.Value.
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.TypeKind.
Require Import Iron.Language.SystemF2Effect.Store.
Require Import Iron.Language.SystemF2Effect.Step.


(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall se sp sp' ss ss' x x' t e
 ,  WfS se sp ss
 -> TYPEX nil nil se sp x t e
 -> STEP  ss sp x ss' sp' x'
 -> (exists se' e'
            ,  extends se' se
            /\ WfS   se' sp' ss'
            /\ SubsT e e'
            /\ TYPEX nil nil se' sp' x' t e').
Proof.
 intros se sp sp' ss ss' x x' t e HH HT HS. gen t e.
 induction HS; intros; inverts_type; rip.


 Case "EsLet".
  spec IHHS t e1. rip.
  shift se'.
  destruct H as [e1'].
  exists (TSum e1' e2).
  inverts HH.
  rip.
   inverts H; burn.
   inverts H; burn.
   inverts H; burn.
   inverts H. rip.
    eapply TxLet; eauto.


 Case "EsLetSubst".
  exists se. exists e2.
  rip.
  burn.
  eapply subst_val_exp; eauto.


 Case "EsAppSubst".
  exists se. exists e.
  rip.
  eapply subst_val_exp; eauto.


 Case "EsLAMSubst".
  exists se. exists (TBot KEffect).
  rip.
  assert (TYPEX nil (substTE 0 t2 nil) (substTE 0 t2 se) sp
                (substTX 0 t2 x12) 
                (substTT 0 t2 t12)     (substTT 0 t2 (TBot KEffect))).
   eapply subst_type_exp; eauto.

   inverts HH. rip. eauto.
   rrwrite (liftTE 0 nil = nil).
   rrwrite (liftTE 0 se  = se). 
   auto.

   inverts HH. rip. eauto.
   rrwrite (substTE 0 t2 nil = nil).
   rrwrite (substTE 0 t2 se  = se).
   norm.


 Case "EsNew".
  remember (TCon (TyConRegion (length sp))) as r.
  exists se.
  exists e.
  rip.

  (* Store with the new region handle property is well formed. *)
  assert (WfS se (SRegion <: sp) ss).
   inverts HH. rip.
    unfold STORET in *.
    lets D: (@Forall2_impl stbind). eauto.
  auto.

  (* Result expression is well typed. *)
  inverts HH; rip. 
  rrwrite (liftTE 0 nil = nil).
  rrwrite (liftTE 0 se  = se).

  have   (KIND nil r KRegion)
   by (subst; eauto).

  have   (TYPEX nil (substTE 0 r nil) (substTE 0 r se) sp
                    (substTX 0 r x)   (substTT 0 r t0) (substTT 0 r e0))
   by (eapply subst_type_exp; eauto).

  rrwrite (substTE 0 r nil = nil).
  rrwrite (substTE 0 r se  = se).

  have ST: (substTT 0 r t0  = t) by admit. (* ok, no free var 0 due to lowerTT 0 t0 = Some t *)
  have SE: (substTT 0 r e0  = e) by admit. (* likewise *)
  rewrite ST in H5.
  rewrite SE in H5.
  eauto.


 Case "EsUse".
  spec IHHS H7.
  shift se'. shift e'.
  rip; inverts H; rip.


 Case "EsUsePop".
  exists se.
  exists (TBot KEffect).
  rip.


 Case "EsAlloc".
  set (tRef' := tRef (TCon (TyConRegion r1)) t2).
  exists (tRef' <: se).
  exists (TBot KEffect).
  inverts HH. rip.

  (* Extended store environment is closed.
     Done manually to avoid non-instantiated existentials. *)
  assert (closedT t2).
   unfold closedT.
   rrwrite (0 = @length ki nil).
   apply (kind_wfT nil t2 KData).
    apply (typex_kind_type nil nil se sp (XVal v1) t2 (TBot KEffect)).
    auto.
  subst tRef'. auto.

  (* Extended store is well typed. *)
  subst tRef'. eauto.

  (* Resulting location is well typed.
     Done manually to avoid non-instantiated existentials. *)
  apply TxVal.
  apply TvLoc.
   unfold tRef'. 
   inverts_kind.
   rrwrite (length ss = length se).
    auto.
   apply KIApp with (k11 := KData).
    unfold appkind. burn.
    
   apply KIApp with (k11 := KRegion).
    unfold appkind. burn.
    auto. auto.

   apply (typex_kind_type nil nil se sp (XVal v1) t2 (TBot KEffect)).
   auto.


 Case "EsRead".
  exists se.
  exists (TBot KEffect).
  rip.
  eapply TxVal.
  inverts HH. rip.
  unfold STORET in *.
  admit.                                (* ok, has type via get ss/ get se *)


 Case "EsWrite".
  exists se.
  exists (TBot KEffect).
  rip.
  inverts HH. rip.
  unfold STORET in *.
  admit.                                (* store env models update store *)
  admit.                                (* updated store is typed under store env *)


 Case "EsSucc".
  exists se.
  exists (TBot KEffect).
  burn.


 Case "EsIsZeroTrue".
  exists se.
  exists (TBot KEffect).
  burn.
Qed.


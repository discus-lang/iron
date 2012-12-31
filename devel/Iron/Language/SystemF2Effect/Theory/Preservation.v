
Require Import Iron.Language.SystemF2Effect.Theory.SubstValExp.
Require Import Iron.Language.SystemF2Effect.Kind.
Require Import Iron.Language.SystemF2Effect.Type.
Require Import Iron.Language.SystemF2Effect.Value.
Require Import Iron.Language.SystemF2Effect.Store.
Require Import Iron.Language.SystemF2Effect.Step.


(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall se s x s' x' t e
 ,  WfS se s
 -> TYPEX nil nil se x  t e
 -> STEP s x s' x'
 -> (exists se' e'
            ,  extends se' se
            /\ WfS  se' s'
            /\ SubsT e e'
            /\ TYPEX nil nil se' x' t e').
Proof.
 intros se s x s' x' t e HH HT HS. gen t e.
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
   inverts H.
    eapply TxLet; auto.
    eapply typex_stenv_extends; eauto.

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
  assert (TYPEX nil (substTE 0 t2 nil) (substTE 0 t2 se)
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

 Case "EsAlloc".
  exists (tRef (TCon (TyConRegion r1)) t2 <: se).
  exists (TBot KEffect).
  rip.
  inverts HH. rip; burn.
  burn.

 Case "EsRead".
  exists se.
  exists (TBot KEffect).
  burn.

 Case "EsWrite".
  exists se.
  exists (TBot KEffect).
  burn.

 Case "EsSucc".
  exists se.
  exists (TBot KEffect).
  burn.

 Case "EsIsZeroTrue".
  exists se.
  exists (TBot KEffect).
  burn.
Qed.


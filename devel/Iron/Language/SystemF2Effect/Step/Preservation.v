
Require Export Iron.Language.SystemF2Effect.Step.TfJudge.

Definition WfFS (ss : store) (se : stenv) (fs : stack) (sp : stprops) 
 := Forall closedT se
 /\ STOREP fs sp
 /\ STOREM se ss
 /\ STORET se sp ss.


(* When a well typed expression transitions to the next state
   then its type is preserved. *)
Theorem preservation
 :  forall ss ss' se fs sp fs' x x' t e
 ,  WfFS   ss se fs sp
 -> TYPEC  nil nil se fs  x   t  e
 -> STEPF  ss  fs  x  ss' fs' x'
 -> (exists se' sp' e'
            ,  extends se' se
            /\ WfFS  ss' se' fs' sp'
            /\ SubsT e e'
            /\ TYPEC nil nil se' fs' x' t e').
Proof.
 intros ss ss' se fs sp fs' x x' t e HH HC HS. gen sp t e.
 induction HS; intros; inverts_typec; rip.

 (* Pure evaluation. *)
 Case "SfStep".
  exists se. 
  exists sp. 
  exists (TSum e1 e2).
  rip.
  eapply TcExp; eauto.
  eapply stepp_preservation; eauto.
   inverts HH. rip.

 (* Push let context. *)
 Case "SfLetPush".
  admit.

 (* Pop let context and substitute. *)
 Case "SfLetPop".
  admit.

 (* Create a new region. *)
 Case "SfRegionNew".
  set (r := TCap (TyCapRegion p)).
  exists se.
  exists (sp :> SRegion p).
  exists (TSum (substTT 0 r e) e2).
  rip.
   (* Store is well formed under new props. *)
   admit.   (* ok, WfFs under extended props *)

   admit.   (* NO PRES OF EFFECTS
               We get phase-changed effects for regions in current stack
               because we're inside the use context *)

   (* Result is well typed. *)
   eapply TcExp 
       with (sp := sp0 :> SRegion p) 
            (t1 := substTT 0 r t0).
     admit. (* ok, store props model new frame stack *)
     
     (* Type is preserved after substituting handle. *)
     rrwrite (nil = substTE 0 r nil).
     rrwrite (se  = substTE 0 r se) by admit. (* ok, se is closed *)
     eapply subst_type_exp with (k2 := KRegion).
      rrwrite (substTE 0 r nil = nil).
      rrwrite (substTE 0 r se  = se)  by admit.
      rrwrite (liftTE 0 nil    = nil).
      rrwrite (liftTE 0 se     = se)  by admit.
      admit.  (* ok, weak store props *)
      subst r. eapply KiCap. 
       admit. (* ok, lists *)

     (* New frame stack is well typed. *)
     eapply TfConsUse.
      admit. (* ok, region handle is fresh, goodness of allocRegionFs *)
      admit. (* ok, t0 doesn't mention ^0 by lowerTT *)
  
 (* Pop a region from ths stack. *)
 Case "SfRegionPop".
  destruct sp.
   false. admit.
   destruct s.
    have (n = p) by admit. subst. (* ok from WfSS *)
  exists se.
  exists sp.
  exists e2.
  rip.
   admit. (* ok, store well formed under reduced props *)
   admit. (* ok, effect subs, bot *)
   
   destruct sp0.
    false. admit.
    destruct s.
     have (n = p) by admit. subst. (* ok, from WfSS *)

   rrwrite (e2 = TSum (TBot KEffect) e2) by admit.
   eapply TcExp with (t1 := t1).
    have (STOREP fs sp0) by admit. (* ok, from WfSS *)
    eauto.
    eapply TxVal.
     admit. (* ok, get p notin t1 from TYPEF, maybe add premise to TYPEF *)
     rrwrite (TSum (TBot KEffect) e2 = e2) by admit.
      auto.

 (* Allocate a reference. *)
 Case "SfStoreAlloc".
  admit.

 (* Read from a reference. *)
 Case "SfStoreRead".
  admit.

 (* Write to a reference. *)
 Case "SfStoreWrite".
  admit.
Qed.


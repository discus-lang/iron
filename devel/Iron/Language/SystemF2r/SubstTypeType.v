
Require Import Iron.Language.SystemF2r.KiJudge.


(* Substitution of types in types preserves kinding.
   Must also subst new new type into types in env higher than ix
   otherwise indices that reference subst type are broken, and 
   the resulting type env would not be well formed *)
Theorem subst_type_type_ix
 :  forall ix ke ke' t1 k1 t2 k2
 ,  keKi   ix k2 ke ke'
 -> KIND ke' t1 k1
 -> KIND ke  t2 k2
 -> KIND ke  (substTT ix t2 t1) k1.
Proof.
 intros. gen ix ke ke' t2 k1 k2.
 induction t1; intros; simpl; inverts_kind; eauto.

 Case "TVar".
  fbreak_nat_compare.
  SCase "n = ix".
   admit. (* ok, keKi keAtK lemma *)

  SCase "n < ix".
   apply KIVar. 
   admit. (* ok, need get_delete_above. *)

  SCase "n > ix".
   apply KIVar.
   admit. (* need get_delete_below. *)

 Case "TForall".
  admit.
Qed.


Theorem subst_type_type_ix_forall2
 :  forall ix ke ke' t2 k2 ts ks
 ,  keKi ix k2 ke ke'
 -> Forall2 (KIND ke') ts ks
 ->          KIND ke t2 k2
 -> Forall2 (KIND ke) (map (substTT ix t2) ts) ks.
Proof.
 intros.
 eapply Forall2_map_left.
 apply (Forall2_impl
            (fun t k => KIND ke' t k)
            (fun t k => KIND ke (substTT ix t2 t) k)
            ts ks).
  intros. eapply subst_type_type_ix; eauto.
  eauto.
Qed.  


Theorem subst_type_type
 :  forall ke ke' t1 k1 t2 k2
 ,  keK k2 ke ke'
 -> KIND ke' t1 k1
 -> KIND ke  t2 k2
 -> KIND ke (substTT 0 t2 t1) k1.
Proof.
 intros.
 unfold substTT.
 admit.
Qed.


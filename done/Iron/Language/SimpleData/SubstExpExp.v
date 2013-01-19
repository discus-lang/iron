
Require Import Iron.Language.SimpleData.TyJudge.
Require Import Iron.Language.SimpleData.ExpSubst.
Require Export Iron.Language.SimpleData.Exp.


(* Substitution of values in values. 
   Inductively, we must reason about performing substitutions at any
   depth, hence we must prove a property about (subst' d x2 x1) instead
   of the weaker (subst x2 x1) which assumes the substitution is taking
   place at top level. *)
Theorem subst_exp_exp_ix
 :  forall ix ds te x1 x2 t1 t2
 ,  get  ix te = Some t2
 -> TYPE ds te           x1 t1
 -> TYPE ds (delete ix te) x2 t2
 -> TYPE ds (delete ix te) (substX ix x2 x1) t1.
Proof.
 intros. gen ix ds te x2 t1 t2.
 induction x1 using exp_mutind with 
  (PA := fun a1 => forall ix ds te x2 t11 t12 t2
      ,  get ix te = Some t2
      -> TYPEA ds te           a1 t11 t12
      -> TYPE  ds (delete ix te) x2 t2
      -> TYPEA ds (delete ix te) (substA ix x2 a1) t11 t12)
  ; intros; simpl; inverts_type; eauto.

 Case "XVar".
  fbreak_nat_compare; burn.

  SCase "n > ix".
   apply TYVar.
   destruct n; burn.
   norm. down. apply get_delete_below. omega.
   
 Case "XLam".
  apply TYLam.
  rewrite delete_rewind.
  eauto using type_tyenv_weaken1.

 Case "XCon".
  eapply TYCon; burn.
   norm.
   apply (Forall2_map_left (TYPE ds (delete ix te))).
   apply (Forall2_impl_in  (TYPE ds te)); eauto.

 (* Case expressions *)
 Case "XCase".
  eapply TYCase; eauto.
   clear IHx1.

   (* Alts have correct type *)
   eapply Forall_map. burn.

   (* There is at least one alt *)
   rewrite map_length; burn.

   (* Required datacon is in alts list *)
   norm.
   rename x into d.
   rewrite map_map. unfold Basics.compose.
   apply in_map_iff.
   have (exists a, dcOfAlt a = d /\ In a aa). 
   shift a. rip.
   rewrite dcOfAlt_substA; auto.

 Case "AAlt".
  eapply TYAlt; auto.
  rewrite delete_app.
  eapply IHx1; eauto.
  rewrite <- delete_app.
  eauto using type_tyenv_weaken_append.
Qed.


Theorem subst_exp_exp
 :  forall ds te x1 x2 t1 t2
 ,  TYPE ds (te :> t2) x1 t1
 -> TYPE ds te         x2 t2 
 -> TYPE ds te (substX 0 x2 x1) t1.
Proof. 
 intros ds te x1 x2 t1 t2 Ht1 Ht2.
 lets H: subst_exp_exp_ix 0 (te :> t2).
  simpl in H. eauto.
Qed.


(* Substitution of several expressions at once. *)
Theorem subst_exp_exp_list
 :  forall ds te x1 xs t1 ts
 ,  Forall2 (TYPE ds te)         xs ts
 -> TYPE ds (te >< ts) x1 t1
 -> TYPE ds te    (substXs 0 xs x1) t1.
Proof.
 intros ds te x1 xs t1 ts HF HT.
 gen ts x1.
 induction xs; intros; inverts_type; simpl.

 Case "base case".
  destruct ts; burn.

 Case "step case".
  destruct ts; burn.
  simpl in *.
  inverts HF.
  eapply IHxs. eauto.
  eapply subst_exp_exp; eauto.
  rrwrite (length xs = length ts).
  burn using type_tyenv_weaken_append.
Qed.

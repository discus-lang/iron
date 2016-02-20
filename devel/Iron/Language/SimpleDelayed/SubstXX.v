
Require Export Iron.Language.SimpleDelayed.TypeX.


(* Apply an expression substitution to an expression. *)
Fixpoint substXX (ss: @subst exp ty) (xx: exp) {struct xx} : exp  :=
 match xx with
 | XVar n
 => match lookupSubst n ss with
    | None                => xx
    | Some (BBind _ _ x)  => x
    end

 |  XAbs ss2 n t x
 => XAbs (ss >< mapExpOfSubst (substXX ss) ss2) n t x

 |  XApp x1 x2
 => XApp (substXX ss x1) (substXX ss x2)
 end.


(* Substitution of expressions in expressions preserves typing.

   Inductively, we must reason about performing substitutions at any
   depth, hence we must prove a property about (subst' d x2 x1) instead
   of the weaker (subst x2 x1) which assumes the substitution is taking
   place at top level. 
*)
Lemma subst_exp_exp
 :  forall te ss x t
 ,  TypeX  (te >< stripS ss) x t
 -> ForallSubstXT (TypeX te) ss
 -> TypeX  te (substXX ss x) t.
Proof.
 intros. gen te ss t.
 induction x using exp_iind;
  intros; simpl in *; inverts_type.

 - Case "XVar".
   remember (lookupSubst n ss) as o.
   symmetry in Heqo.
   destruct o.

   + SCase "variable matches".
     destruct b.
     eapply lookup_env_subst_some; eauto.

     assert (n = n0) as HN.
     eapply (@lookupSubst_name exp ty); eauto.
     rewrite HN in *.
     eauto.

   + SCase "variable does not match.".
     eapply TxVar.
     eapply lookup_env_subst_none; eauto.

 - Case "XLam".
   eapply TxLam.
   + eapply ForallSubstXT_app; auto.

     eapply (Forall_inst te)  in H.
     eapply (Forall_inst ss0) in H.
     eapply (Forall_mp_const) in H; auto.

     eapply (Forall_map 
              (  fun xx => forall t
              ,  TypeX (te >< stripS ss0) xx t
              -> TypeX te (substXX ss0 xx) t)) in H.

     eapply Forall_Forall2_right  in H.
     eapply ForallSubstXT_fold    in H.

     eapply ForallSubstXT_mapExpOfSubst.
     eapply ForallSubstXT_mp; eauto.

   + unfold stripS.
     rewrite map_app.
     rewrite stripS_fold.
     rewrite stripS_mapExpOfSubst.
     rewrite <- app_assoc.
     assumption.

 - Case "XApp".
   eapply TxApp; eauto.
Qed.


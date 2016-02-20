
Require Export Iron.Language.DelayedSystemF.TypeX.


(* Apply an expression substitution to an expression. *)
Fixpoint substXX (ss: @subst exp ty) (xx: exp) {struct xx} : exp  :=
 match xx with
 | XVar n
 => match lookupSubst n ss with
    | None                => xx
    | Some (BBind _ _ x)  => x
    end

 |  XAbs sx n t x
 => XAbs (ss >< mapExpOfSubst (substXX ss) sx) n t x

 |  XApp x1 x2
 => XApp (substXX ss x1) (substXX ss x2)

 |  XABS st sx a k x
 => XABS st (ss >< mapExpOfSubst (substXX ss) sx) a k x

 |  XAPP x1 t2 
 => XAPP (substXX ss x1) t2
 end.


(* Substitution of expressions in expressions preserves typing. *)
Lemma subst_exp_exp
 :  forall ke te sx x t
 ,  TypeX  ke (te >< stripS sx) x t
 -> ForallSubstXT (TypeX ke te) sx
 -> TypeX  ke te (substXX sx x) t.
Proof.
 intros. gen ke te sx t.
 induction x using exp_iind;
  intros; simpl in *.

 - Case "XVar".
   inverts_type.
   remember (lookupSubst n sx) as o.
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

 - Case "XAbs".
   inverts_type.
   eapply TxAbs.
   + eapply ForallSubstXT_app; auto.

     eapply (Forall_inst ke)  in H.
     eapply (Forall_inst te)  in H.
     eapply (Forall_inst sx0) in H.
     eapply (Forall_mp_const) in H; auto.

     eapply (Forall_map 
              (  fun xx => forall t
              ,  TypeX ke (te >< stripS sx0) xx t
              -> TypeX ke te (substXX sx0 xx) t)) in H.

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
   inverts_type.
   eapply TxApp; eauto.

 - Case "XABS".
   destruct t; nope.
   destruct k. destruct k0.
   inverts_type.
   eapply TxABS.
   unfold stripS.
   rewrite map_app.
   repeat (rewrite stripS_fold).
   rewrite stripS_mapExpOfSubst.
   rewrite <- app_assoc.
   destruct k1.
   assumption.

 - Case "XAPP".
   inverts_type.
   eapply TxAPP.
   eapply IHx; auto.
Qed.



Require Export Iron.Language.SimpleDelayed.TypeX.


(* Lookup the type of the given variable from a substitution. *)
Fixpoint lookupSubstX (var: nat) (ss: substx) : option bind :=
 match ss with
 | nil                
 => None

 | BBind v t x :: rest
 => if beq_nat var v
      then Some (BBind v t x)
      else lookupSubstX var rest
 end.


(* Apply an expression substitution to an expression. *)
Fixpoint substXX (ss: substx) (xx: exp) : exp :=
 match xx with
 | XVar n
 => match lookupSubstX n ss with
    | None                => xx
    | Some (BBind _ _ x)  => x
    end

 |  XAbs ss2 n t x
 => XAbs (ss >< map (substXB ss) ss2) n t x

 |  XApp x1 x2
 => XApp (substXX ss x1) (substXX ss x2)
 end

 with substXB (ss: substx) (bb: bind): bind :=
       match bb with
       | BBind n t x => BBind n t (substXX ss x)
       end.


Lemma map_stripB_substXB
 : forall bs1 bs2
 , map stripB (map (substXB bs1) bs2)
 = map stripB bs2.
Proof.
 intros.
 induction bs2.
 simpl. auto.
 simpl. rewrite IHbs2.
 destruct a. simpl. auto.
Qed.


Lemma lookupSubstX_name 
 :  forall n1 n2 t e bs
 ,  lookupSubstX n1 bs = Some (BBind n2 t e)
 -> n1 = n2.
Proof.
 intros.
 induction bs.
 - simpl in *. nope.
 - simpl in *. destruct a.
   remember (n1 =? n) as X. destruct X.
   + inverts H. eapply beq_nat_true. firstorder.
   + firstorder.
Qed.


Lemma lookup_env_subst_none
 :  forall n te bs t
 ,  lookupEnv n (te >< map stripB bs) = Some t
 -> lookupSubstX n bs                 = None
 -> lookupEnv n te = Some t.
Proof.
 intros.
 induction bs.
 - simpl in *. nope.
 - simpl in *. destruct a. simpl in H.
   remember (n =? n0) as X. destruct X.
   + inverts H.
     nope.
   + eapply IHbs. 
     * auto. 
     * assumption.
Qed.


Lemma lookup_env_subst_some
 :  forall n te bs e t t0
 ,  Forall (TypeB te) bs
 -> lookupEnv    n (te >< map stripB bs) = Some t
 -> lookupSubstX n bs                    = Some (BBind n t0 e)
 -> TypeX te e t.
Proof.
 intros. gen n te e t t0.
 induction bs; intros.
 - simpl in *. nope.
 - simpl in *. destruct a. simpl in *.
   remember (n =? n0) as X. destruct X.
   + inverts H0. inverts H1.
     inverts H.  inverts H2. assumption.
   + inverts H; eauto.
Qed.


(* Substitution of expressions in expressions preserves typing.

   Inductively, we must reason about performing substitutions at any
   depth, hence we must prove a property about (subst' d x2 x1) instead
   of the weaker (subst x2 x1) which assumes the substitution is taking
   place at top level. 
*)
Lemma subst_exp_exp
 :  forall te bs x t
 ,  TypeX  (te >< map stripB bs) x t
 -> Forall (TypeB te) bs
 -> TypeX  te (substXX bs x) t.
Proof.
 intros. gen te bs t.
 induction x using exp_mutind with
  (PB := fun b => forall te bs
      ,  TypeB (te >< map stripB bs) b
      -> Forall (TypeB te) bs
      -> TypeB te (substXB bs b))
   ; intros; simpl in *; inverts_type.

 - Case "XVar".
   remember (lookupSubstX n bs) as X.
   destruct X.

   + SCase "variable matches".
     destruct b.
     symmetry in HeqX.
     eapply (lookup_env_subst_some n te bs e t t0) in H3; eauto.
     lets D: lookupSubstX_name HeqX. inverts D. assumption.

   + SCase "variable does not match.".
     eapply TxVar.
     eapply lookup_env_subst_none; eauto.

 - Case "XLam".
   eapply TxLam.
   + eapply Forall_app; auto.
     * eapply (Forall_insts te)  in H.
       eapply (Forall_insts bs0) in H.
       eapply (Forall_impls 
               (fun b => TypeB (te >< map stripB bs0) b)) in H; auto.
       eapply (Forall_impl_inner (Forall (TypeB te) bs0)) in H; auto.

   + rewrite map_app.
     rewrite map_stripB_substXB.
     rewrite <- app_assoc.
     assumption.

 - Case "XApp".
   eapply TxApp; eauto.

 - Case "BBind".
   eapply TsSig; eauto.
Qed.


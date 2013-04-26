
Require Import Iron.Language.SystemF2Data.Type.
Require Import Iron.Language.SystemF2Data.Exp.Relation.TypeX.
Require Import Iron.Language.SystemF2Data.Exp.Operator.LiftTX.


(* Substitution of Types in Exps *)
Fixpoint substTX (d: nat) (u: ty) (xx: exp) : exp :=
  match xx with
  |  XVar _     => xx

  |  XLAM x     
  => XLAM (substTX (S d) (liftTT 1 0 u) x)

  |  XAPP x t
  => XAPP (substTX d u x)  (substTT d u t)

  |  XLam t x
  => XLam (substTT d u t)  (substTX d u x)

  |  XApp x1 x2
  => XApp (substTX d u x1) (substTX d u x2)

  |  XCon dc ts xs 
  => XCon dc (map (substTT d u) ts) (map (substTX d u) xs)

  |  XCase xx alts
  => XCase (substTX d u xx) (map (substTA d u) alts)

  |  XPrim p xs
  => XPrim p (map (substTX d u) xs)

  |  XLit l    => xx
 end

with substTA (d: nat) (u: ty) (aa: alt) : alt :=
  match aa with
  |  AAlt dc xx
  => AAlt dc (substTX d u xx)
  end.


(* The data constructor of an alternative is unchanged
   by type substitution. *)
Lemma dcOfAlt_substTA
 : forall d u a
 , dcOfAlt (substTA d u a) = dcOfAlt a.
Proof.
 intros. destruct a. destruct d0. auto.
Qed.
Hint Rewrite dcOfAlt_substTA : global.


Theorem subst_type_exp_ix
 :  forall ix ds ke te x1 t1 t2 k2
 ,  get ix ke = Some k2
 -> TYPE ds ke  te x1 t1
 -> KIND (delete ix ke)  t2 k2
 -> TYPE ds (delete ix ke)     (substTE ix t2 te)
            (substTX ix t2 x1) (substTT ix t2 t1).
Proof.
 intros. gen ix ds ke te t1 t2 k2.
 induction x1 using exp_mutind with 
  (PA := fun a => forall ix ds ke te t1 t2 t3 k3
      ,  get ix ke = Some k3
      -> TYPEA ds ke te a t1 t2
      -> KIND (delete ix ke) t3 k3
      -> TYPEA ds (delete ix ke)  (substTE ix t3 te) (substTA ix t3 a)
                  (substTT ix t3 t1) (substTT ix t3 t2));
  intros; simpl; inverts_type; eauto.

 - Case "XVar".
   apply TYVar.
   unfold substTE. auto. 

 - Case "XLAM".
   simpl. apply TYLAM.
   rewrite delete_rewind.
   rewrite (liftTE_substTE 0 ix).
   eauto using kind_kienv_weaken.

 - Case "XAPP".
   rewrite (substTT_substTT 0 ix).
   eauto using subst_type_type_ix.
   apply TYAPP.
   + simpl. eapply (IHx1 ix) in H4; eauto.
   + simpl. eapply subst_type_type_ix; eauto.

 - Case "XLam".
   simpl. 
   apply TYLam.
   + eapply subst_type_type_ix; eauto.
   + unfold substTE. rewrite map_rewind.
     rrwrite ( map (substTT ix t2) (te :> t)
             = substTE ix t2 (te :> t)).
     eapply IHx1; eauto.

 - Case "XApp".
   eapply TYApp.
   + eapply IHx1_1 in H4; eauto.
     simpl in H4. burn.
   + eapply IHx1_2 in H6; eauto.

 - Case "XCon".
   rr. simpl.
   eapply TYCon; eauto.
   + eapply subst_type_type_ix_forall2; eauto.
   + eapply Forall2_map.
     eapply Forall2_map_right' in H11.
     eapply Forall2_impl_in; eauto; intros.
     rrwrite (ix = 0 + ix). 
     rewrite substTTs_substTT; rr.
     * norm. eapply H; eauto.
     * defok ds (DefData     dc tsFields tc).
       defok ds (DefDataType tc ks       dcs).
       rrwrite (length ts = length ks).
       norm.
       have (KIND ks y KStar). eauto.
 
 - Case "XCase".
   eapply TYCase; eauto.
   + eapply Forall_map.
     norm. eauto.
   + norm.
     have (In x (map dcOfAlt aa)).
     assert ( map dcOfAlt (map (substTA ix t2) aa)
            = map dcOfAlt aa) as HDC.
     lists. f_equal.
     extensionality x0. rr. auto.
     rewrite HDC. auto.

 - Case "XPrim".
   eapply TYPrim; eauto.
   + lets D: prim_types_closed H5. rip.
     rrwrite (substTT ix t2 t1 = t1). 
     eauto.
   + have (Forall closedT tsArg) 
      by (eapply prim_types_closed_args; eauto).

     have HTS: (tsArg = map (substTT ix t2) tsArg)
      by (symmetry; eauto; eapply substTT_closedT_id_list; eauto).
     rewrite HTS.
     rewrite HTS in H7.

     eapply Forall2_map.
     eapply Forall2_map_right' in H7.
     eapply Forall2_impl_in; eauto; intros. 
     simpl in H6.
     snorm.
     eapply H; eauto. 
     have (closedT y).
     rrwrite (substTT ix t2 y = y) in H6.
     trivial.     

 - Case "XLit".
   eapply TYLit.
   destruct l; snorm.

 - Case "AAlt".
   defok ds (DefData dc tsFields tc).
   rr.
   eapply TYAlt with (tc := tc) (ks := ks) (dcs := dcs); eauto.
   eapply subst_type_type_ix_forall2; eauto.
    eapply IHx1 in H10; eauto.
    rrwrite (ix = 0 + ix).   
    rewrite substTTs_substTT_map; rr.
    + unfold substTE. 
      rewrite <- map_app. auto. 
    + rrwrite (length tsParam = length ks).
      eauto.
Qed.


Theorem subst_type_exp
 :  forall ds ke te x1 t1 t2 k2
 ,  TYPE ds (ke :> k2) te x1 t1
 -> KIND ke  t2 k2
 -> TYPE ds ke (substTE 0 t2 te) (substTX 0 t2 x1) (substTT 0 t2 t1).
Proof.
 intros. 
 rrwrite (ke = delete 0 (ke :> k2)).
 eapply subst_type_exp_ix; burn.
Qed.


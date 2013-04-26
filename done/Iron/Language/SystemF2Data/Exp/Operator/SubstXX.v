
Require Import Iron.Language.SystemF2Data.Type.
Require Import Iron.Language.SystemF2Data.Exp.Relation.TypeX.


(* Substitution of Exps in Exps *)
Fixpoint substXX (d:  nat) (u: exp) (xx: exp) : exp :=
 match xx with
    | XVar ix 
    => match nat_compare ix d with
       (* Index matches the one we are substituting for. *)
       | Eq  => u
       
       (* Index was free in the original expression.
          As we've removed the outermost binder, also decrease this
          index by one. *)
       | Gt  => XVar (ix - 1)

       (* Index was bound in the original expression. *)
       | Lt  => XVar ix
       end

    |  XLAM x1
    => XLAM (substXX d (liftTX 0 u) x1)

    |  XAPP x1 t2
    => XAPP (substXX d u x1) t2

    (* Increase the depth as we move across a lambda.
       Also lift free references in the exp being substituted
       across the lambda as we enter it. *)
    |  XLam t1 x2
    => XLam t1 (substXX (S d) (liftXX 1 0 u) x2)

    |  XApp x1 x2 
    => XApp (substXX d u x1) (substXX d u x2)
 
    |  XCon dc ts xs
    => XCon dc ts (map (substXX d u) xs)

    |  XCase x alts
    => XCase (substXX d u x) (map (substXA d u) alts)

    |  XPrim p xs
    => XPrim p (map (substXX d u) xs)

    |  XLit l
    => xx
    end

with substXA (d: nat) (u: exp) (aa: alt) 
 := match aa with 
    |  AAlt (DataCon tag arity) x 
    => AAlt (DataCon tag arity)
         (substXX (d + arity) 
                  (liftXX arity 0 u) x)
    end. 


(* The data constructor of an alternative is unchanged
   by exp substitution. *)
Lemma dcOfAlt_substXA
 : forall d u a
 , dcOfAlt (substXA d u a) = dcOfAlt a.
Proof.
 intros. destruct a. destruct d0. auto.
Qed.
Hint Rewrite dcOfAlt_substXA : global.


(* Substitution of exps in exps preserves typing *)
Theorem subst_exp_exp_ix
 :  forall ix ds ke te x1 t1 x2 t2
 ,  get  ix te = Some t2
 -> TYPE ds ke te           x1 t1
 -> TYPE ds ke (delete ix te) x2 t2
 -> TYPE ds ke (delete ix te) (substXX ix x2 x1) t1.
Proof.
 intros. gen ix ds ke te t1 x2 t2.
 induction x1 using exp_mutind with 
  (PA := fun a1 => forall ix ds ke te x2 t11 t12 t2
      ,  get ix te = Some t2
      -> TYPEA ds ke te           a1 t11 t12
      -> TYPE  ds ke (delete ix te) x2 t2
      -> TYPEA ds ke (delete ix te) (substXA ix x2 a1) t11 t12);
  intros; simpl; inverts_type; eauto.

 - Case "XVar".
   fbreak_nat_compare.
   SCase "n = ix".
    rewrite H in H3. inverts H3. auto.

  + SCase "n < ix".
    apply TYVar; auto.

  + SCase "n > ix".
    apply TYVar; auto.
    rewrite <- H3.
    destruct n.
    * burn. 
    * simpl. rrwrite (n - 0 = n) by omega. 
      apply get_delete_below; burn.

 - Case "XLAM".
   simpl.
   eapply (IHx1 ix) in H3.
   + apply TYLAM.
     unfold liftTE. rewrite map_delete. eauto.
   + eapply get_map. eauto.
   + unfold liftTE. rewrite <- map_delete.
     rrwrite ( map (liftTT 1 0) (delete ix te) 
             = liftTE 0 (delete ix te)). 
     apply type_kienv_weaken1. auto.

 - Case "XLam".
   simpl.
   apply TYLam; auto.
    rewrite delete_rewind.
    eauto using type_tyenv_weaken1.

 - Case "XCon".
   eapply TYCon; eauto.
    apply (Forall2_map_left (TYPE ds ke (delete ix te))).
    apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
    snorm. eauto.

 - Case "XCase".
   eapply TYCase; eauto.
   (* Alts have correct type *)
   + clear IHx1.
     eapply Forall_map.
     norm. eauto.

   (* Required datacon is in alts list *)
   + norm. 
     rename x into d. lists.
     apply in_map_iff.
     have (exists a, dcOfAlt a = d /\ In a aa). 
      shift a. rip.
     rewrite dcOfAlt_substXA; auto.

 - Case "XPrim".
   eapply TYPrim; eauto.
    apply (Forall2_map_left (TYPE ds ke (delete ix te))).
    apply (Forall2_impl_in  (TYPE ds ke te)); eauto.
    snorm. eauto.

 - Case "AAlt".
   defok ds (DefData dc tsFields tc).
   eapply TYAlt; eauto.
   rewrite delete_app.
   lists.
   assert ( length tsFields 
          = length (map (substTTs 0 tsParam) tsFields)) as HL
    by (lists; auto).
   rewrite HL.
   eapply IHx1 with (t2 := t2); eauto.
   rewrite <- delete_app.
   eauto using type_tyenv_weaken_append.
Qed.


Theorem subst_exp_exp
 :  forall ds ke te x1 t1 x2 t2
 ,  TYPE ds ke (te :> t2) x1 t1
 -> TYPE ds ke te x2 t2
 -> TYPE ds ke te (substXX 0 x2 x1) t1.
Proof.
 intros.
 rrwrite (te = delete 0 (te :> t2)). 
 eapply subst_exp_exp_ix; burn.
Qed.


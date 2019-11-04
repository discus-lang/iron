
Require Export Iron.Language.Calc.Ty.
Require Export Iron.Language.Calc.Eval.


(* If some term m has type t,
   then when we evaluate it the result also has type t *)
Lemma soundness
  : forall m t
  , TYPE m t -> (exists v, EVAL m v /\ TYPE (MVal v) t).
Proof.
 intro m.
 induction m; intros.

 (* value *)
 - exists v;   auto.


 (* add *)
 - inversion H; subst.

   eapply IHm1 in H2; destruct H2 as [v1']; rip.
   assert (exists n1', v1' = VNat n1') as N1.
    apply canonical_value_nat; auto.
   destruct N1 as [n1']. subst.

   eapply IHm2 in H4; destruct H4 as [v2']; rip.
   assert (exists n2', v2' = VNat n2') as N2.
    apply canonical_value_nat; auto.
   destruct N2 as [n2']. subst.

   exists (VNat (n1' + n2')); rip.
   + eapply EvAdd; auto.
   + eapply TyNat.


 (* less *)
 - inversion H; subst.

   eapply IHm1 in H2; destruct H2 as [v1']; rip.
   assert (exists n1', v1' = VNat n1') as N1.
    apply canonical_value_nat; auto.
   destruct N1 as [n1']. subst.

   eapply IHm2 in H4; destruct H4 as [v2']; rip.
   assert (exists n2', v2' = VNat n2') as N2.
    apply canonical_value_nat; auto.
   destruct N2 as [n2']. subst.

   exists (VBool (blt_nat n1' n2')); rip.
   + eapply EvLess; auto.
   + eapply TyBool.


 (* and *)
 - inversion H; subst.

   eapply IHm1 in H2; destruct H2 as [v1']; rip.
   assert (exists b1', v1' = VBool b1') as B1.
    apply canonical_value_bool; auto.
   destruct B1 as [b1']. subst.

   eapply IHm2 in H4; destruct H4 as [v2']; rip.
   assert (exists b2', v2' = VBool b2') as B2.
    apply canonical_value_bool; auto.
   destruct B2 as [b2']. subst.

   exists (VBool (andb b1' b2')); rip.
   + eapply EvAnd; auto.
   + eapply TyBool.


 (* if *)
 - inversion H; subst.

   (* eval the scrutinee *)
   eapply IHm1 in H3. destruct H3 as [v1']; rip.
   assert (exists b1', v1' = VBool b1') as B1.  
    apply canonical_value_bool; auto.
   destruct B1 as [b1']. subst.
   destruct b1'.

   (* scrutinee is true *)
   + eapply IHm2 in H5. destruct H5 as [v2']; rip.
     exists v2'; auto.

   (* scrutinee is false *)
   + eapply IHm3 in H6. destruct H6 as [v3']; rip.
     exists v3'; auto.
Qed.



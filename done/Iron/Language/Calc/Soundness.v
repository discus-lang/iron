
Require Export Iron.Language.Calc.Ty.
Require Export Iron.Language.Calc.Eval.


(* If some expression e has type t,
   then when we evaluate it the result also has type t *)
Lemma Soundness
  : forall e t
  , TYPE e t -> (exists v, EVAL e v /\ TYPE v t).
Proof.
 intros. gen t. induction e; intros.

 - exists (XNum  n);   auto.
 - exists (XBool b);   auto.
 - exists (XString s); auto.

 (* add *)
 - inverts H. rip.

   eapply IHe1 in H2. destruct H2 as [e1']. rip.
   assert (VALUE  e1'). eauto. 
   assert (exists n1', e1' = XNum n1') as N1. auto.
   destruct N1 as [n1']. subst.

   eapply IHe2 in H4. destruct H4 as [e2']. rip.
   assert (VALUE  e2'). eauto.
   assert (exists n2', e2' = XNum n2') as N2. auto.
   destruct N2 as [n2']. subst.

   exists (XNum (n1' + n2')). rip.

 (* mul *)
 - inverts H. rip.

   eapply IHe1 in H2. destruct H2 as [e1']. rip.
   assert (VALUE  e1'). eauto. 
   assert (exists n1', e1' = XNum n1') as N1. auto.
   destruct N1 as [n1']. subst.

   eapply IHe2 in H4. destruct H4 as [e2']. rip.
   assert (VALUE  e2'). eauto.
   assert (exists n2', e2' = XNum n2') as N2. auto.
   destruct N2 as [n2']. subst.

   exists (XNum (n1' * n2')). rip.

 (* less *)
 - inverts H. rip.

   eapply IHe1 in H2. destruct H2 as [e1']. rip.
   assert (VALUE  e1'). eauto. 
   assert (exists n1', e1' = XNum n1') as N1. auto.
   destruct N1 as [n1']. subst.

   eapply IHe2 in H4. destruct H4 as [e2']. rip.
   assert (VALUE  e2'). eauto.
   assert (exists n2', e2' = XNum n2') as N2. auto.
   destruct N2 as [n2']. subst.

   exists (XBool (blt_nat n1' n2')). rip.

 (* more *)
 - inverts H. rip.

   eapply IHe1 in H2. destruct H2 as [e1']. rip.
   assert (VALUE  e1'). eauto. 
   assert (exists n1', e1' = XNum n1') as N1. auto.
   destruct N1 as [n1']. subst.

   eapply IHe2 in H4. destruct H4 as [e2']. rip.
   assert (VALUE  e2'). eauto.
   assert (exists n2', e2' = XNum n2') as N2. auto.
   destruct N2 as [n2']. subst.

   exists (XBool (bgt_nat n1' n2')). rip.

 (* and *)
 - inverts H. rip.

   eapply IHe1 in H2. destruct H2 as [e1']. rip.
   assert (VALUE  e1'). eauto. 
   assert (exists b1', e1' = XBool b1') as N1. auto.
   destruct N1 as [b1']. subst.

   eapply IHe2 in H4. destruct H4 as [e2']. rip.
   assert (VALUE  e2'). eauto.
   assert (exists b2', e2' = XBool b2') as N2. auto.
   destruct N2 as [b2']. subst.

   exists (XBool (andb b1' b2')). rip.

 (* or *)
 - inverts H. rip.

   eapply IHe1 in H2. destruct H2 as [e1']. rip.
   assert (VALUE  e1'). eauto. 
   assert (exists b1', e1' = XBool b1') as N1. auto.
   destruct N1 as [b1']. subst.

   eapply IHe2 in H4. destruct H4 as [e2']. rip.
   assert (VALUE  e2'). eauto.
   assert (exists b2', e2' = XBool b2') as N2. auto.
   destruct N2 as [b2']. subst.

   exists (XBool (orb b1' b2')). rip.

 (* if *)
 - inverts H. rip.

   (* eval the scrutinee *)
   eapply IHe1 in H3. destruct H3 as [e1']. rip.
   assert (VALUE e1'). eauto.
   assert (exists b1', e1' = XBool b1') as B1. auto.
   destruct B1 as [b1']. subst.
   destruct b1'.

   (* scrutinee is true *)
   eapply IHe2 in H5. destruct H5 as [e2']. rip.
   assert (VALUE e2'). eauto.
   exists e2'. rip.

   (* scrutinee is false *)
   eapply IHe3 in H6. destruct H6 as [e3']. rip.
   assert (VALUE e3'). eauto.
   exists e3'. rip.
Qed.


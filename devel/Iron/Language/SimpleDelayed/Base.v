
Require Export Iron.Data.List.
Require Export Iron.Tactics.Case.
Require Export Iron.Tactics.Nope.
Require Export Iron.Tactics.LibTactics.
Require Export Coq.Arith.Compare_dec.


Lemma Forall_impl
 :  forall A {B} (P: B -> Prop) xs
 ,  A
 -> Forall (fun x => A -> P x) xs
 -> Forall (fun x => P x) xs.
Proof.
 intros.
 induction xs.
 - auto.
 - eapply Forall_cons.
   + inverts H. auto.
   + inverts H. auto.
Qed. 


Lemma Forall_insts
 :  forall {A B} a' xs (P: A -> B -> Prop)
 ,  Forall (fun x => forall a, P a x) xs
 -> Forall (fun x => P a' x) xs.
Proof.
 intros.
 induction xs.
 - auto.
 - eapply Forall_cons.
   + inverts H. eapply H2.
   + inverts H. eapply IHxs. assumption.
Qed.


Lemma Forall_impls
 :  forall {A} (P Q: A -> Prop) xs
 ,  Forall (fun x => P x) xs
 -> Forall (fun x => P x -> Q x) xs
 -> Forall (fun x => Q x) xs.
Proof.
 intros.
 induction xs.
 - auto.
 - eapply Forall_cons.
   + inverts H. inverts H0.
     auto.
   + inverts H. inverts H0. 
     eapply IHxs. auto. auto.
Qed.



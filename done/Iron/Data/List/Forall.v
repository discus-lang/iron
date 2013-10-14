
Require Import Iron.Data.List.Base.
Require Import Iron.Tactics.


(********************************************************************)
(* Lemmas: Forall *)
Lemma Forall_in
 :  forall {A} (P: A -> Prop) x xs
 ,  Forall P xs
 -> In x xs
 -> P x.
Proof.
 intros. gen x.
 induction xs; intros.
 - inverts H0.
 - inverts H0.
   + inverts H. eauto.
   + inverts H. eauto.
Qed.


Lemma Forall_get
 :  forall {A} (P: A -> Prop) ix x xs
 ,  Forall P xs
 -> get ix xs = Some x
 -> P x.
Proof.
 intros. gen x xs.
 induction ix; intros.
  destruct xs.
   false.
   simpl in H0. inverts H0. inverts H. auto.
  destruct xs.
   false.
   simpl in H0.
   eapply IHix.
    inverts H. eapply H4. auto.
Qed.


Lemma Forall_impl_in
 : forall {A}
          (P1: A -> Prop) (P2: A -> Prop)
          (xs: list A)
 ,  (forall x, In x xs -> P1 x -> P2 x)
 -> Forall P1 xs
 -> Forall P2 xs.
Proof.
 intros.
 induction xs.
  auto. 
  inverts H0. intuition.
Qed.


Lemma Forall_snoc
 :  forall {A} (P: A -> Prop) x xs
 ,  P x
 -> Forall P xs
 -> Forall P (x <: xs).
Proof.
 intros. gen x.
 induction xs; intros. 
  simpl. auto.
  simpl. 
   eapply Forall_cons. 
    inverts H0. auto.
   eapply IHxs.
    inverts H0. auto. auto.
Qed.
Hint Resolve Forall_snoc.



Lemma Forall_split_cons
 :  forall {A} P (x : A) xs
 ,  Forall P (x :: xs)
 -> P x /\ Forall P xs.
Proof.
 intros.
  rewrite Forall_forall in H.
  rewrite Forall_forall.
  split; eauto.
Qed.
Hint Resolve Forall_split_cons.


Lemma Forall_app
 :  forall {A} (P: A -> Prop) xs ys
 ,  Forall P xs
 -> Forall P ys
 -> Forall P (xs ++ ys).
Proof.
 intros. 
 rewrite Forall_forall in *.
 intros.
 apply in_app_split in H1.
  firstorder.
Qed.
Hint Resolve Forall_app.


Lemma Forall_app_left
 :  forall {A} (P: A -> Prop) xs ys
 ,  Forall P (xs ++ ys)
 -> Forall P xs.
Proof.
 intros. 
 rewrite Forall_forall in *.
 eauto.
Qed.
Hint Resolve Forall_app_left.


Lemma Forall_app_right
 :  forall {A} (P: A -> Prop) xs ys
 ,  Forall P (xs ++ ys)
 -> Forall P ys.
Proof.
 intros. 
 rewrite Forall_forall in *.
 eauto.
Qed.
Hint Resolve Forall_app_right.


Lemma Forall_map
 :  forall {A B}
           (P: B -> Prop) (f: A -> B) 
           (xs: list A)
 ,  Forall (fun x => P (f x)) xs
 -> Forall P (map f xs).
Proof.
 intros. induction xs.
  apply Forall_nil.
  inverts H. simpl. intuition.
Qed.
Hint Resolve Forall_map.

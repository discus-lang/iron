
Require Export Iron.Data.List.Base.
Require Export Iron.Tactics.


Fixpoint max_list (xs : list nat) :=
 match xs with
 |  nil     => 0
 |  x :: xs => max x (max_list xs)
 end.


Lemma max_ge_left1
 : forall a b
 , max a b >= a.
Proof.
 intros. gen b.
 induction a; intros.
  omega.
  simpl. break b.
   omega.
   cut (max a X >= a). 
    intros. omega.
   eauto.
Qed.
Hint Resolve max_ge_left1.


Lemma max_ge_right1
 : forall a b
 , max a b >= b.
Proof.
 intros. gen b. 
 induction a; intros.
  simpl. auto.
  simpl. destruct b.
   omega.
   spec IHa b. omega.
Qed.
Hint Resolve max_ge_right1.


Lemma max_ge_left
 : forall a b c
 , c >= max a b -> c >= a.
Proof.
 intros. gen b c.
 induction a; intros.
  simpl in *. omega.
   simpl in *. break b.
   subst. auto.
   destruct c.
    nope.
    have (c >= max a X) by omega.
    lets D: IHa H0. omega.
Qed.
Hint Resolve max_ge_left.


Lemma max_ge_right
 : forall a b c
 , c >= max a b -> c >= b.
Proof.
 intros. gen b c.
 induction a; intros.
  simpl in *. subst. auto.
  simpl in *. destruct b.
   omega.
   destruct c.
    nope.
    have (c >= max a b) by omega.
    lets D: IHa H0. omega.
Qed.
Hint Resolve max_ge_right.


Lemma max_ge_above_left
 :  forall a b c
 ,  a >= b
 -> max a c >= b.
Proof.
 intros. gen c b.
 induction a; intros. 
  simpl. omega.
  simpl. destruct c.
   omega.
   destruct b.
    omega.   
    cut (max a c >= b). 
     intros. omega.
     eapply IHa. omega.
Qed. 
Hint Resolve max_ge_above_left.


Lemma max_ge_above_right
 :  forall a b c
 ,  a >= b
 -> max c a >= b.
Proof.
 intros. gen a b.
 induction c; intros. 
  simpl. auto.
  simpl. break a.
   omega.
   subst.
   destruct b.   
    omega.   
    have (X >= b) by omega.
    spec IHc H0. omega.
Qed. 
Hint Resolve max_ge_above_right.


Lemma max_weaken_left
 :  forall a b c
 ,        a >= b
 -> max c a >= b.
Proof.
 intros. gen a b.
 induction c; intros.
  simpl. auto.
  simpl. destruct a.
   omega.
   destruct b.
    omega.
    cut (max c a >= b). intros. omega.
     eapply IHc. omega.
Qed.
Hint Resolve max_weaken_left.


(********************************************************************)
(* Lemmas: max_list *)

Lemma max_list_above
 :  forall xs
 ,  Forall (fun x => max_list xs >= x) xs.
Proof.
 intros.
 induction xs; unfold not; intros.
  - simpl. auto.
  - eapply Forall_cons.
    + simpl. eauto.

    + eapply Forall_impl
       with (P := (fun x => max_list xs >= x)); eauto.
      intros.
      simpl.
      remember (max_list xs) as mx.
      eapply max_weaken_left. auto.
Qed.
Hint Resolve max_list_above.


Lemma max_list_succ_not_in
 :  forall xs
 ,  not (In (S (max_list xs)) xs).
Proof.
 intros.
 unfold not. intros.
 lets D1: max_list_above xs.
  rewrite Forall_forall in D1.
 spec D1 H. omega.
Qed.
Hint Resolve max_list_succ_not_in.


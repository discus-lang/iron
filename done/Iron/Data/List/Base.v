
Require Export Coq.Lists.List.
Require Import Iron.Data.Nat.
Require Import Iron.Tactics.


(* Unfolding defs from Coq.Lists.List module *)
Hint Unfold length.
Hint Unfold app.
Hint Unfold firstn.
Hint Unfold skipn.


(********************************************************************)
(* Definitions *)

(* Add a single element to the end of the list *)
Fixpoint snoc {A: Type} (x: A) (xx: list A) : list A :=
 match xx with 
 | nil       => x :: nil
 | y :: xs'  => y :: snoc x xs'
 end.


(* Get an indexed element from a list, starting from 0.
   This is like the Coq 'nth' function, but returns an option instead
   of a provided default value. Using an option is useful when we simply
   want to determine whether some element is in the list, but don't
   need the actual value *)
Fixpoint get {A: Type} (i: nat) (e: list A) {struct e}: option A :=
 match e, i with
 | x :: _,  O     => Some x
 | _ :: xs, S i'  => get  i' xs
 | _, _           => None
 end.


(********************************************************************)
(* Environment notations.
   These look more natural than the standard operators when dealing
   with de-Bruijn environments. *)
Notation "xs :> x"  := (x :: xs)   (at level 61, left associativity).
Notation "x  <: xs" := (snoc x xs) (at level 62, right associativity).
Notation "xs >< ys" := (app ys xs) (at level 60, right associativity).


(********************************************************************)
(** Lemmas: cons/snoc *)

Lemma cons_snoc_empty
 :  forall A (x: A)
 ,  x <: nil = nil :> x.
Proof. 
 auto.
Qed.
Hint Resolve cons_snoc_empty.


Lemma snoc_cons
 :  forall A (xs: list A) (x: A) (y: A)
 ,  ((x <: xs) :> y) = (x <: (xs :> y)).
Proof.
 intros. destruct xs; auto.
Qed.
Hint Resolve snoc_cons.


Lemma snocable
 : forall {A} (ts: list A)
 , ts = nil \/ (exists t ts', ts = snoc t ts').
Proof.
 intros.
 induction ts.
  auto.
  inverts IHts.
   right. eauto.
   right. dest t. dest ts.
    subst. eauto.
Qed.


(********************************************************************)
(** Lemmas: length *)

(* A list with length zero is always nil. *)
Lemma length_zero_is_nil
 :  forall {A} (xx: list A)
 ,  length xx = O 
 -> xx = nil.
Proof.
 intros. 
 destruct xx; burn.
Qed.
Hint Resolve length_zero_is_nil.


Lemma length_simpl_snoc
 : forall {A} x (xs: list A)
 , length (x <: xs) = 1 + length xs.
Proof. 
 induction xs; burn.
Qed.
Hint Resolve length_simpl_snoc.


Lemma get_length_snoc
 :  forall {A} (xs : list A) (x : A)
 ,  get (length xs) (x <: xs) = Some x.
Proof.
 intros. gen x.
 induction xs; burn.
Qed.
Hint Resolve get_length_snoc.


Lemma get_length_less_snoc
 :  forall {A} i x (xs : list A)
 ,  i < length xs
 -> get i (x <: xs) = get i xs.
Proof.
 intros. gen i.
 induction xs; intros.
  destruct i. 
   nope.
   auto.
  destruct i.
   auto.
   simpl.
   simpl in H.
   assert (i < length xs). omega.
   eauto.
Qed.
Hint Resolve get_length_less_snoc.


(* If there is an element at a particular index, then the length
   of the list is bigger than that index. *)
Lemma get_length_more
 :  forall A n (xx: list A) x
 ,  get n xx = Some x 
 -> length xx > n.
Proof.
 intros. gen xx.
 induction n; intros.
  destruct xx.
   false. 
   simpl in H. inverts H. simpl. omega.
   
  destruct xx.
   false.
   simpl in H. apply IHn in H. simpl. omega.
Qed.
Hint Resolve get_length_more.


Lemma get_length_less
 :  forall A n (xx: list A) x
 ,  get n xx = Some x
 -> n < length xx.
Proof.
 eapply get_length_more.
Qed.
Hint Resolve get_length_less.


Lemma get_length_less_exists
 :  forall {A} i (xs : list A)
 ,  i < length xs
 -> exists x, get i xs = Some x.
Proof.
 intros. gen xs.
 induction i; intros.
  destruct xs. 
   nope.
   simpl in H. burn.
  destruct xs.
   simpl in H. nope.
   simpl in H.
   simpl. eapply IHi.
    burn.
Qed.
Hint Resolve get_length_less_exists.


Lemma get_none_length
 :  forall {A} n (xs: list A)
 ,  get n xs = None
 -> length xs <= n.
Proof.
 intros. gen n.
 induction xs; intros.
  simpl. burn.
  simpl. simpl in H.
   destruct n.
    false.
    apply IHxs in H. omega.
Qed.
Hint Resolve get_none_length.


Lemma length_in_in_nonempty
 :  forall {A} xs1 xs2
 ,  (forall (x: A), In x xs1 -> In x xs2)
 -> length xs1 > 0
 -> length xs2 > 0.
Proof.
 intros.
 destruct xs1.
  nope.
  destruct xs2.
   have (In a (xs1 :> a)).
   spec H a. rip. nope.
   simpl. omega.
Qed.
Hint Resolve length_in_in_nonempty.


(********************************************************************)
(** Lemmas: app *)

Lemma app_nil_left
 :  forall A (xx: list A)
 ,  nil ++ xx = xx.
Proof.
 auto.
Qed.
Hint Resolve app_nil_left.
Hint Rewrite app_nil_left : global.


Lemma app_nil_right
 :  forall A (xx: list A)
 ,  xx ++ nil = xx.
Proof. 
 intros.
 induction xx. 
  auto.
  simpl. rewrite IHxx. trivial.
Qed.
Hint Resolve app_nil_right.
Hint Rewrite app_nil_right : global.


Lemma app_snoc
 :  forall A (l1: list A) (l2: list A) (x : A)
 ,  ((l1 :> x) >< l2) = l1 >< (x <: l2).
Proof. 
 intros.
 induction l2.
  auto.
  simpl. rewrite IHl2. auto.
Qed.
Hint Resolve app_snoc.


Lemma app_snoc'
 :  forall A (l1: list A) (l2: list A) (x : A)
 ,  (x <: l1) >< l2 = x <: (l1 >< l2).
Proof.
 intros.
 induction l2.
  auto.
  simpl. rewrite IHl2. auto.
Qed.
Hint Resolve app_snoc'.


Lemma app_cons_nil_left
 :  forall A x (yy: list A)
 ,  (x :: nil) ++ yy
 =  x :: yy.
Proof.
 intros.
 simpl. auto.
Qed.
Hint Resolve app_cons_nil_left.
Hint Rewrite app_cons_nil_left : global.


Lemma app_cons_nil_right
 :  forall A y (xx: list A)
 ,  xx ++ (y :: nil)
 =  snoc y xx.
Proof.
 intros.
 rewrite app_snoc. rr.
 auto.
Qed.
Hint Resolve app_cons_nil_right.
Hint Rewrite app_cons_nil_right : global.


Lemma app_length
 :  forall A (l1: list A) l2
 ,  length (l1 ++ l2) = length l1 + length l2.
Proof.
 intros.
 induction l1.
  auto.
  simpl. rip.
Qed.
Hint Rewrite app_length : global.


Lemma length_snoc 
 :  forall A (xs: list A) x
 ,  length (x <: xs)  = 1 + length xs.
Proof.
 intros.
 assert (x <: xs = (x :: nil) >< xs).
  rewrite app_snoc.
  rewrite app_nil_right. auto.

 rewrite H.
 rewrite app_length.
 simpl. omega.
Qed.
Hint Rewrite length_snoc : global.


(********************************************************************)
(** Lemmas: get *)

Lemma get_rewind
 :  forall A n x (xx: list A)
 ,  get n xx = get (S n) (xx :> x).
Proof. auto. Qed.
Hint Resolve get_rewind.


(* If we can get an element from a list then it is in that list. *)
Lemma get_in
 :  forall A (xs: list A) x n
 ,  get n xs = Some x -> In x xs.
Proof.
 intros.
  gen x xs. 
  induction n; intros.
   destruct xs. 
    false.
    simpl in H. inverts H. simpl. auto.
   destruct xs.
    simpl in H. false.
    simpl in H. simpl. right. auto.
Qed.
Hint Resolve get_in.


(* If a list contains an element at a non-zero index, 
   then it also contains an element at the previous index. *)
Lemma get_succ_some
 :  forall A (xx: list A) n
 ,  (exists t, get (S n) xx = Some t)
 -> (exists t, get n xx     = Some t).
Proof.
 intros. gen n.
 induction xx; intros.
  simpl in H. inverts H. inverts H0.
  destruct n; simpl; eauto.
Qed.
Hint Resolve get_succ_some.


(* If a list contains an element at a non-zero index, 
   then it also contains an element at the previous index. *)
Lemma get_minus1
 :  forall A n x (xx: list A)
 ,  n > 0
 -> get n (xx :> x) = get (n - 1) xx.
Proof.
 intros. destruct n.
  inverts H.
  simpl. norm_nat. trivial.
Qed.
Hint Resolve get_minus1.


(* If a list contains an element at a particular index,
   then if we add a new element to the end of the list
   then it still contains the original element at that same index. *)
Lemma get_snoc_some
 :  forall A (xx: list A) n x1 x2
 ,  get n xx         = Some x1
 -> get n (x2 <: xx) = Some x1.
Proof.
 intros. gen n.
 induction xx; intros.
  destruct n.
   simpl in H. false.
   simpl in H. false.
  destruct n. 
   simpl in H. simpl. trivial. 
   simpl in H. simpl. apply IHxx. trivial.
Qed.
Hint Resolve get_snoc_some.


(* If a list contains an element at a particular index,
   then if we append more elements to the end of the ilst
   then it still contains the original element at that same index. *)
Lemma get_app_some
 :  forall A (l1: list A) (l2: list A) n x1
 ,  get n l1         = Some x1 
 -> get n (l1 ++ l2) = Some x1.
Proof.
 intros. gen l1.
 induction l2; intros.
  rewrite app_nil_right. auto.
  rewrite app_snoc. 
   eapply IHl2. apply get_snoc_some. auto.
Qed.
Hint Resolve get_app_some.


Lemma get_cons_some
 :  forall A n (e1: list A) x1 x2
 ,  get n e1               = Some x2
 -> get (n + 1) (e1 :> x1) = Some x2.
Proof.
 intros.
 destruct n.
  simpl. auto.
  simpl. norm_nat. auto.
Qed.
Hint Resolve get_cons_some.


Lemma get_app_left_some
 :  forall A n (e1 e2: list A) x1
 ,  get  n e1                      = Some x1
 -> get (n + length e2) (e2 ++ e1) = Some x1.
Proof.
 intros.
 induction e2.
  simpl. norm_nat. auto.
  assert ((e2 :> a) ++ e1 = (e2 ++ e1) :> a). 
   simpl. auto.
  rewrite H0.
  assert (n + length (e2 :> a) = ((n + length e2) + 1)).
   norm_nat. simpl. auto.
  rewrite H1.
  rewrite <- (get_cons_some A (n + length e2) (e2 ++ e1) a).
   auto. auto.
Qed.
Hint Resolve get_app_left_some.


Lemma get_length_snoc_some
 : forall A x (xs: list A)
 , get (length xs) (x <: xs) = Some x.
Proof.
 intros.
 induction xs; simpl; auto.
Qed.
Hint Resolve get_length_snoc_some.
Hint Rewrite get_length_snoc_some : global.


(* We cannot get elements from a list at indices the same, or larger, 
   than the length of that list *)
Theorem get_above_false
 :  forall A n (xx: list A) t
 ,  n >= length xx
 -> get n xx = Some t 
 -> False.
Proof.
 intros. gen n t.
 induction xx; intros.
  simpl in H0. false.
  destruct n.
   simpl in H0. inverts H0. inverts H.
   simpl in H0. simpl in H.
   assert (n >= length xx). omega.
   eapply IHxx in H1. false. eauto.
Qed.
Hint Resolve get_above_false.


Lemma get_zero_nonempty_some
 :  forall {A} (us: list A)
 ,  length us > 0
 -> (exists x, get 0 us = Some x).
Proof.
 intros.
 destruct us.
  simpl in H. inverts H.
  simpl. eauto.
Qed.
Hint Resolve get_zero_nonempty_some.


Lemma get_same_length
 :  forall {A B} (xs: list A) x (ys: list B) i
 ,  length xs = length ys
 -> get i xs  = Some x
 -> exists y, get i ys = Some y.
Proof.
 intros. gen ys x i.
 induction xs; intros.
  have (ys = nil).
   subst. nope.
  destruct ys.
   nope.
   have (length xs = length ys).
   spec IHxs H1.
   destruct i.
    simpl in H0.
     inverts H0.
     exists b. eauto.
    simpl in H0.
    simpl. 
    spec IHxs H0. auto.
Qed.
Hint Resolve get_same_length.


Lemma get_in_exists
 :  forall {A} (x : A) (xs : list A)
 ,  In x xs -> exists n, get n xs = Some x.
Proof.
 intros.
 induction xs.
  nope.
  simpl in H. inverts H.
   exists 0. simpl. auto.
   spec IHxs H0.
   destruct IHxs as [n].
   exists (S n).
   simpl. auto.
Qed.
Hint Resolve get_in_exists.


(********************************************************************)
(** Lemmas: in *)
Lemma in_head
 :  forall {A} (x : A) xs
 ,  In x (x :: xs).
Proof. firstorder. Qed.
Hint Resolve in_head.


Lemma in_tail
 :  forall {A} (a : A) b xs
 ,  a <> b
 -> In a (b :: xs) -> In a xs.
Proof.
 intros.
 apply get_in_exists in H0.
 destruct H0 as [n].
  destruct n.
  simpl in H0. inverts H0. tauto.
  simpl in H0. eapply get_in. eauto.
Qed. 
Hint Resolve in_tail.


Lemma in_split
 :  forall {A} (x y : A) (xs : list A)
 ,  In x xs \/ x = y -> In x (y :: xs).
Proof.
 intros. inverts H.
  apply get_in_exists in H0.
  destruct H0 as [n]. 
  apply get_in with (n := S n).
  simpl. auto.
  firstorder.
Qed.
Hint Resolve in_split.


Lemma in_snoc 
 :  forall {A} x a (xs: list A)
 ,  In x xs 
 -> In x (a <: xs).
Proof.
 intros.
 induction xs.
  nope.
  simpl in H.
   inverts H.
   simpl. auto.
   simpl. eauto.
Qed.
Hint Resolve in_snoc.


Lemma in_app_split
 :  forall {A} (x : A) xs ys
 ,  In x (xs ++ ys)
 -> In x xs \/ In x ys.
Proof.
 intros.
 induction xs.
  - simpl.
    right. simpl in H. auto.
  - rrwrite ((ys >< (xs :> a)) = (ys >< xs) :> a) in H.
    simpl in H.
    inverts H. 
    + left. auto.
    + rip.
      inverts IHxs.
      * left.
        auto.
      * rip.
Qed.
Hint Resolve in_app_split.


Lemma in_snoc_split
 :  forall {A} (x : A) y ys
 ,  In x (y <: ys)
 -> x = y \/ In x ys.
Proof.
 intros.
 rrwrite (y <: ys = (nil :> y) >< ys) in H.
 eapply in_app_split in H.
 inverts H.
 - tauto.
 - inverts H0.
   + tauto.
   + inverts H.
Qed.
Hint Resolve in_snoc_split.


Lemma in_app_left
 :  forall {A} x (xs ys: list A)
 ,  In x xs
 -> In x (xs ++ ys).
Proof.
 intros.
 eapply (@rev_ind A (fun ys => In x (xs ++ ys))); intros.
  rr. auto.
  rr. rrwrite ((x0 <: l) >< xs = (x0 <: (l >< xs))). eauto.
Qed.
Hint Resolve in_app_left.


Lemma in_app_right
 :  forall {A} x (xs ys: list A)
 ,  In x ys
 -> In x (xs ++ ys).
Proof.
 intros.
 induction xs.
  rr. auto.
  rrwrite ((a :: xs) ++ ys = a :: (xs ++ ys)).
  apply in_cons. auto.
Qed.
Hint Resolve in_app_right.


Lemma in_app_comm
 :  forall {A} (x : A) xs ys
 ,  In x (xs ++ ys)
 -> In x (ys ++ xs).
Proof.
 intros. gen ys.
 induction xs; intros.
  - rewrite app_nil_left in H.
    rewrite app_nil_right.
    auto.
  - simpl in H.
    inverts H.
    + rrwrite ((xs :> x) >< ys = xs >< (x <: ys)).
      eapply IHxs. eauto.
    + rrwrite ((xs :> a) >< ys = xs >< (a <: ys)).
      eapply in_app_split in H0.
      inverts H0.
      * apply in_app_right. auto.
      * apply in_app_left. auto.
Qed.
Hint Resolve in_app_comm.


Lemma in_not_in
 :  forall {A} (y z : A) xs
 ,    In y xs
 -> ~(In z xs)
 -> ~(y = z).
Proof.
 unfold not in *.
 intros. subst. auto.
Qed.     
Hint Resolve in_not_in.



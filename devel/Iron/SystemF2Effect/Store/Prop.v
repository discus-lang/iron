
Require Import Iron.SystemF2Effect.Base.

Inductive stprop :=
 (* A region descriptor.
    One of these exists in the store for every live region in the store. *)
 | SRegion : nat -> stprop.


Definition stprops 
 := list stprop.



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
    snorm. omega.
   eauto.
Qed.


Lemma max_ge_above
 : forall a b c
 ,  a >= b
 -> max c a >= b.
Proof.
 intros. gen a b.
 induction c; intros. 
  snorm.
  snorm. break a.
   omega.
   subst.
   destruct b.   
    omega.   
    have (X >= b) by omega.
    spec IHc H0. omega.
Qed. 


Lemma max_ge_left
 : forall a b c
 , c >= max a b -> c >= a.
Proof.
 intros. gen b c.
 induction a; intros.
  snorm.
   snorm. break b.
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
  snorm. subst. auto.
  simpl in H.
  destruct b.
   simpl in H. subst. auto.
   destruct c.
    nope.
    have (c >= max a b) by omega.
    lets D: IHa H0. omega.
Qed.
Hint Resolve max_ge_right.


Lemma max_list_above
 :  forall xs
 ,  Forall (fun x => max_list xs >= x) xs.
Proof.
 intros.
 induction xs; unfold not; intros.
  snorm.
  eapply Forall_cons.
   snorm. eauto.
   eapply Forall_impl
    with (P := (fun x => max_list xs >= x)); eauto.
   intros.
   simpl.
   remember (max_list xs) as mx.
   eapply max_ge_above. auto.
Qed.


Lemma max_list_succ_not_in
 :  forall xs
 ,  not (In (S (max_list xs)) xs).
Proof.
 intros.
 unfold not. intros.
 lets D1: max_list_above xs.
 norm.
 spec D1 H. omega.
Qed.


Lemma list_in_map
 :  forall {A B} (x : A) (xs : list A) (f : A -> B)
 ,  In x xs -> In (f x) (map f xs).
Proof.
 intros. gen x f.
 induction xs; intros.
  simpl. auto.
  simpl. simpl in H.
   inverts H.
    left.  auto.
    right. auto.
Qed.


Fixpoint regionOfStProp (s : stprop) : option nat :=
 match s with
 | SRegion n       => Some n
 end.


Fixpoint catOptions {A} (xs : list (option A)) : list A
 := match xs with
    | nil             => nil
    | Some x :: rest  => x :: catOptions rest
    | None   :: rest  => catOptions rest
    end.


Definition allocRegion (sp : stprops) : nat 
 := S (max_list (catOptions (map regionOfStProp sp))).


Lemma max_weaken_left
 :  forall a b c
 ,        a >= b
 -> max c a >= b.
Proof.
 intros. gen a b.
 induction c; intros.
  snorm.
  simpl. destruct a.
   omega.
   destruct b.
    omega.
    cut (max c a >= b). intros. omega.
     eapply IHc. omega.
Qed.


Lemma allocRegion_weaken
 :  forall sp s n
 ,  allocRegion sp        >= n
 -> allocRegion (sp :> s) >= n.
Proof.
 intros.
  destruct n.
  omega.
  unfold allocRegion in *.
   snorm.
   have (max_list (catOptions (map regionOfStProp sp)) >= n) by omega. clear H.
   cut  (max n0 (max_list (catOptions (map regionOfStProp sp))) >= n).
    intros. omega.
    apply max_weaken_left. 
    auto.
Qed.
 

Lemma allocRegion_above
 : forall sp
 , Forall (fun s => match regionOfStProp s with
                    | Some n => allocRegion sp > n
                    | None   => True
                    end)
          sp.
Proof.
 induction sp; intros.
  snorm.
  snorm.
  inverts H.
   destruct x.
    snorm.
    unfold allocRegion.
     simpl.
     remember (max_list (catOptions (map regionOfStProp sp))) as X.
     cut (max n0 X >= n0). 
      intros. omega.
     apply max_ge_left1.
   destruct x.
    snorm. 
    spec IHsp H0.
    snorm.
    apply allocRegion_weaken. auto.
Qed.


(* Allocated region is fresh wrt existing store properties. *)
Lemma allocRegion_fresh
 : forall sp
 , not (In (SRegion (allocRegion sp)) sp).
Proof.
 intros.
 unfold not. intros.
 lets D: allocRegion_above sp.
  snorm.
 spec D H.
  snorm. omega.
Qed.
 

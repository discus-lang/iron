
Require Import Iron.SystemF2Effect.Base.

(* Store Property *)
Inductive stprop :=
 (* A region descriptor.
    One of these exists in the store for every live region in the store. *)
 | SRegion : nat -> stprop.


(* Store Properties *)
Definition stprops 
 := list stprop.


(* TODO: shift this into base library *)
Fixpoint elem {A} (p : A -> bool) (xx : list A)
 := match xx with
    | nil      => false
    | x :: xs  => if p x then true else elem p xs
    end.


Lemma elem_get_not
 :  forall {A} (p : A -> bool) (xx : list A) 
 ,  not (exists ix x, get ix xx = Some x /\ p x = true)
 -> elem p xx = false.
Proof. 
 intros.
 induction xx.
 - simpl. auto.
 - remember (p a) as X.
   destruct X.
   + simpl. 
     rewrite <- HeqX.
     assert (exists ix x, get ix (xx :> a) = Some x /\ p x = true).
      exists 0. exists a. rip.
     tauto.
     
   + simpl. 
     rewrite <- HeqX. 
     eapply IHxx.
     unfold not. 
     intros.
     destruct H0 as [ix].
     destruct H0 as [x].
     rip.
     have (get (S ix) (xx :> a) = Some x).
     assert (exists ix x, get ix (xx :> a) = Some x /\ p x = true).
      exists (S ix). exists x. rip.
     tauto.
Qed.  


(********************************************************************)
(* Take a region back from a store property *)
Fixpoint regionOfStProp (s : stprop) : option nat :=
 match s with
 | SRegion n       => Some n
 end.


Definition isSRegion (r : nat) (pp : stprop) : bool
 := match pp with
    | SRegion r' => beq_nat r r'
    end.


Definition hasSRegion (r : nat) (sp : stprops) 
 := elem (isSRegion r) sp.


(********************************************************************)
(* Allocate a fresh region. *)

Fixpoint catOptions {A} (xs : list (option A)) : list A
 := match xs with
    | nil             => nil
    | Some x :: rest  => x :: catOptions rest
    | None   :: rest  => catOptions rest
    end.


Definition allocRegion (sp : stprops) : nat 
 := S (max_list (catOptions (map regionOfStProp sp))).


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
Hint Resolve allocRegion_weaken.


(* A freshly allocated region is greater than all regions already
   in the store properties. *)
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
Hint Resolve allocRegion_fresh.


(* Old store properties do not contain allocated region. *)
Lemma allocRegion_fresh_has
 :  forall p sp
 ,  p = allocRegion sp
 -> hasSRegion p sp = false.
Proof.
 intros.
 subst.
  unfold hasSRegion.
  eapply elem_get_not.
  unfold not. intros.
   destruct H as [ix].
   destruct H as [x].
   rip.
   destruct x.
    simpl in H1.
    snorm. symmetry in H1. subst.
    apply get_in in H0.
    have (not (In (SRegion (allocRegion sp)) sp)) by apply allocRegion_fresh.
    tauto.
Qed.
Hint Resolve allocRegion_fresh_has.


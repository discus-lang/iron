
Require Import Iron.SystemF2Effect.Base.

(* Store Property *)
Inductive stprop :=
 (* A region descriptor.
    One of these exists in the store for every live region in the store. *)
 | SRegion : nat -> stprop.


(* Store Properties *)
Definition stprops 
 := list stprop.


(********************************************************************)
(* Take a region back from a store property *)
Fixpoint regionOfStProp (s : stprop) : option nat :=
 match s with
 | SRegion n       => Some n
 end.


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


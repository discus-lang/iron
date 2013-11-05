
Require Import Iron.Language.SystemF2Effect.Base.


(********************************************************************)
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
 | SRegion p      => Some p
 end.


(* Check if this is a store property with the given
   region identifier. *)
Definition isSRegion (p : nat) (pp : stprop) : bool := 
 match pp with
 | SRegion p' => beq_nat p p'
 end.


(* Check if any of the given store properties include this
   region identifier *)
Definition hasSRegion (p : nat) (sp : stprops) 
 := elem (isSRegion p) sp.


(********************************************************************)
(* Allocate a fresh region. *)
Definition allocRegion (sp : stprops) : nat 
 := S (max_list (catOptions (map regionOfStProp sp))).


Lemma allocRegion_weaken
 :  forall sp s p
 ,  allocRegion sp        >= p
 -> allocRegion (sp :> s) >= p.
Proof.
 intros.
  destruct p.
  omega.
  unfold allocRegion in *.
   snorm.
   have (max_list (catOptions (map regionOfStProp sp)) >= p) 
    by omega. clear H.
   cut  (max n (max_list (catOptions (map regionOfStProp sp))) >= p).
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
                    | Some p => allocRegion sp > p
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
    have (not (In (SRegion (allocRegion sp)) sp)) 
     by apply allocRegion_fresh.
    tauto.
Qed.
Hint Resolve allocRegion_fresh_has.


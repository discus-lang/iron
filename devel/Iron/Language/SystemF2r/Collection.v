(* Typeclassopedia, Brent Yorgey, 2013 

   Stack overflow questions: 
   https://stackoverflow.com/questions/27703340/multiple-typeclass-inheritance-in-coq
   https://stackoverflow.com/questions/7990301/building-a-class-hierarchy-in-coq
*)

Require Import Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Iron.Data.List.
Open Scope list_scope.


(* Monoids **********************************************************)
Class Monoid {A : Type}
    (unit : A)
    (dot  : A -> A -> A) : Prop 
:= {
 dot_assoc : forall x y (z : A)
           , dot x (dot y z) = dot (dot x y) z;

 dot_left  : forall x, dot unit x = x;
 dot_right : forall x, dot x unit = x 
}.


Instance ListMonoid : forall A, @Monoid (list A) nil (@app A).
intros. split.
 - apply app_assoc.
 - apply app_nil_l.
 - apply app_nil_r.
Defined.


(* Collections ******************************************************)
(* 
Definition env = tyenv * kienv * stenv

Instance Sharded env ty
  ... 

Instance Sharded env ki
  ... 

Class Sharded  {C : Type} {A : Type}
    (ins     : nat -> A -> C -> C}
    (idx     : nat -> A -> C -> option A}
*)


(* TODO: rename to Sequence *)
Class Collection {C : Type -> Type} {A : Type}
    (empty   : C A)
    (size    : C A -> nat)
    (append  : C A -> C A -> C A)         (* TODO: derive from ins/idx ? *)
    (ins     : nat -> A -> C A -> C A)
    (idx     : nat -> C A -> option A)

(* `(F       : Foldable (C A) foldr) *)

   `(M       : Monoid (C A) empty append)
:= {
 size_empty  : size empty = 0;

 ins_idx     :  forall i x c
             ,  i < size c 
             -> idx i (ins i x c) = Some x

 (* TODO: What other properties do we need? *)

}.


Instance ListCollection (A : Type) 
  : @Collection list A 
       nil (@length A) (@app A) (@insert A) (@get A)
       (ListMonoid A).
split.
 
 - Case "size_empty".
   simpl. reflexivity.
 
 - Case "ins_idx".
   intros. gen i.
   induction c; simpl.
    + nope.
    + destruct i. 
      * simpl. auto.
      * intros. 
        eapply IHc. omega.
Qed.


(* Collection is formed by adding an element at a given point. *)
Definition also {A} {C} `{Collection C A}
   (i : nat) (x : A) (c : C A) (c' : C A) 
   := c' = ins i x c.


Definition has  {A} {C} `{Collection C A}
   (i : nat) (x : A) (c : C A)
  := idx i c = Some x.


Lemma also_has_above {C} {A} `{Collection C A} 
 : forall n i x1 x2 (xx : C A) xx'
 ,  n < i
 -> has  n x1 xx
 -> also i x2 xx  xx'
 -> has  n x1 xx'.
Proof.
 intros. gen n xx.
 induction i; intros.
 - destruct xx'. 

doesn't work, not inductive 
 - nope.
 - unfold has  in *. 
   unfold also in *.
   subst. eapply ins_idx. 
   eapply IHi.
  **)

(**** TODO: Generalise this to use collections,
      also other functions from Data.List.Insert.
      maybe get_insert_below needs to be a primitive of Collection.

Lemma get_insert_below
 :  forall {A: Type} n ix (xx: list A) x1 x2
 ,  n < ix
 -> get n xx                = Some x1
 -> get n (insert ix x2 xx) = Some x1.
Proof.
 intros. gen n xx.
 induction ix; intros.
  destruct xx.
   false.
   destruct n.
    false. omega.
    false. omega.
  destruct xx.
   false.
   destruct n. 
    simpl in H0. auto.
    simpl in H0. simpl. apply IHix. omega. auto.
Qed.
Hint Resolve get_insert_below.
****)

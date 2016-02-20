

Require Import Iron.Data.Monoid.
Require Import Coq.Program.Basics.


Require Coq.Lists.List.
Module List := Coq.Lists.List.


Class Monoid
  {A     : Type}
  (unit  : A)
  (dot   : A -> A -> A)
:= {
  unit_left 
   : forall x
   , dot unit x = x;

  unit_right
   : forall x
   , dot x unit = x;

  dot_assoc
   : forall x y z
   , dot x (dot y z) = dot (dot x y) z
}.


Class Functor 
  {F     : Type -> Type}
  (map   : forall {a b : Type}, (a -> b) -> F a -> F b)
:= {
  map_id 
   : forall {a} (xx : F a)
   , map id xx = id xx;

  map_map 
   : forall {a b c} (p : b -> c) (q : a -> b) (xx: F a)
   , map (compose p q) xx = compose (map p) (map q) xx
}.


Hint Transparent compose.

Instance FunctorList {a : Type}
 : @Functor list List.map.
Proof.
 split.

 (* map_id *)
 - intros.
   induction xx; simpl.
   + trivial.
   + rewrite IHxx. trivial.

 (* map_map *)
 - intros.
   induction xx; simpl.
   + trivial.
   + rewrite IHxx. unfold compose in *. simpl. trivial. trivial.



   induction xx; unfold compose in *; simpl.
   + trivial.
   + rewrite IHxx. trivial.
Qed.





Class Functor 
  {F    : Type -> Type}
  (map  : forall {a b : Type}, (a -> b) -> F a -> F b)
:= {
  map_id 
   : forall {a} (xx : F a)
   , map id xx = id xx;

  map_map 
   : forall {a b c} (p : b -> c) (q : a -> b) (xx: F a)
   , map (compose p q) xx = compose (map p) (map q) xx
}.


Require Import Coq.Lists.List.

Instance FunctorList {a : Type}
 : @Functor list map.
Proof.
 esplit.

 (* map_id *)
 - intros.
   induction xx.
   + simpl. auto.
   + simpl. rewrite IHxx. auto.

 (* map_map *)
 - intros.
   induction xx.
   + simpl. unfold compose. simpl. auto.
   + simpl. rewrite IHxx. unfold compose. simpl. auto.
Qed.




Class Bag {s: Type -> Type}
  (empty   : forall {a}, s a)
  (size    : forall {a}, s a -> nat)
  (extend  : forall {a}, a   -> s a -> s a)
  (union   : forall {a}, s a -> s a -> s a)
  (member  : forall {a}, a   -> s a -> Prop)
:= {

  size_empty
   : forall x
   , size (@empty x) = 0;

  size_extend
   : forall {a} (x: a) bag
   , size (extend x bag) = S (size bag);

  member_empty
   : forall {a} (x: a)
   , member x empty;

  member_extend
   : forall {a} (x: a) bag
   , member x (extend x bag);

  union_member1
   : forall {a} x (b1 b2: s a)
   ,  member x b1
   -> member x (union b1 b2);

  union_member2
   :  forall {a} x (b1 b2: s a)
   ,  member x b2
   -> member x (union b1 b2)

}.





Class Sequence {s : Type -> Type} {a : Type}
  (empty   : s a)
  (length  : s a -> nat)
  (append  : s a -> s a -> s a)
  (insert  : nat -> a -> s a -> s a)
  (index   : nat -> s a -> option a)
:= {

  length_empty  
   : length empty = 0;

  index_insert_below
   :  forall i j (xx : s a) x1 x2
   ,  i < j
   -> index i xx               = Some x1
   -> index i (insert j x2 xx) = Some x1

}.






(* Get an indexed element from a list, starting from 0.
   This is like the Coq 'nth' function, but returns an option instead
   of a provided default value. Using an option is useful when we simply
   want to determine whether some element is in the list, but don't
   need the actual value *)
Fixpoint get {a} (i: nat) (e: list a) {struct e}: option a :=
 match e, i with
 | x :: _,  O     => Some x
 | _ :: xs, S i'  => get  i' xs
 | _, _           => None
 end.


Fixpoint insert {a} (ix: nat) (x: a) (xs: list a): list a :=
 match ix, xs with
 | _,     nil      => x :: nil
 | S ix', y :: xs' => y :: (insert ix' x xs')
 | 0,     xs'      => x :: xs'
 end.


Require Import Omega.
Require Import LibTactics.

Instance SequenceList {a : Type}
 : @Sequence list a 
     nil (@length a) (@app a) insert (@get a).
Proof.
 esplit.


 (* length_empty *)
 - simpl. auto.

 (* index_insert_below *)
 - intros. gen i xx.
   induction j; intros.
   + destruct xx.
     * simpl in H0. congruence.
     * omega.
   + destruct xx.
     * simpl in H0. congruence.
     * destruct i.
       simpl in H0. inverts H0. simpl. auto.
       simpl. eapply IHj. omega. simpl in H0. auto.
Qed.



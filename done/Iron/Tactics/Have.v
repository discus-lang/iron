
(* Assert a statement and prove it via burn.
   This leads to more structured proving than using plain 'assert', 
   because a 'have' form must always complete the goal. *)

(* This is the default tactic used to prove things.
   It should be overwridden by the client module with something that includes
   domain-specific normalisations. *)
Ltac have_auto := auto.


Tactic Notation "have" constr(E) :=
 let H := fresh 
 in assert E as H by have_auto.

Tactic Notation "have" constr(E) "by" tactic(T) :=
 let H := fresh 
 in assert E as H by T.

Tactic Notation "have" ident(H) ":" constr(E) :=
 assert E as H by have_auto.

Tactic Notation "have" ident(H) ":" constr(E) "by" tactic(T) :=
 assert E as H by T.

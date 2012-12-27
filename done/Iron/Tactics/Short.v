
(* Shorthands for existing tactics *)
Require Import Iron.Tactics.LibTactics.


(* Specializes *)
Tactic Notation "spec" hyp(H1) hyp(H2) 
 := specializes H1 H2.
Tactic Notation "spec" hyp(H1) hyp(H2) hyp(H3)
 := specializes H1 H2 H3.
Tactic Notation "spec" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
 := specializes H1 H2 H3 H4.
Tactic Notation "spec" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
 := specializes H1 H2 H3 H4.
Tactic Notation "spec" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
 := specializes H1 H2 H3 H4 H5.
Tactic Notation "spec" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) hyp(H6)
 := specializes H1 H2 H3 H4 H5 H6.

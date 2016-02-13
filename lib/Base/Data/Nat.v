
Require Import Base.Class.Monoid.
Require Import Coq.Arith.Mult.
Require Import Omega.


Instance Monoid_nat_plus
 : @Monoid nat 0 plus.
Proof. split.

 (* unit_left *)
 - intros. omega.

 (* unit_right *)
 - intros. omega.

 (* dot_assoc *)
 - intros. omega.
Qed.


Instance Monoid_nat_mult
 : @Monoid nat 1 mult.
Proof. split.

 (* unit_left *)
 - intros. omega.

 (* unit_right *)
 - intros. omega.

 (* dot_assoc *)
 - intros. apply mult_assoc.
Qed.


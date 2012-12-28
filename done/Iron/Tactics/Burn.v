
Require Import Iron.Tactics.LibTactics.
Require Import Iron.Tactics.Rewrite.
Require Import Iron.Tactics.Rip.
Require Import Omega.

Ltac rs := rewritess.
Ltac rr := autorewrite with global in *.


(********************************************************************)
(* Burn mega-tactic for semantics proofs.

   * This gets lots of the common cases, where Coq really should 
     have tried a bit harder. For example, trying f_equal before eauto.

   * It also contains cases for patterns that often arise when using
     the deBruijn representation. For example, trying false before
     omega to show that a case concerning index manipulation
     cannot happen.

   * Failing is sometimes slow due to the (firstorder burn0) tactic
     in burn1.
 *)

(* Primitive tactics that fail quickly. *)
Ltac burn0
 := first
    [ assumption       (* Goal is one of the assumptions. *)
    | reflexivity      (* Goal has form e = e. *)
    | solve [eauto]    (* Resolution based proving *)
    | omega            (* Solves inequalities with Presburger arithmetic.  *)
    | false; omega ].  (* Solves inequalities with Presburger arithmetic.  *)

(* Try the firstorder solver.
   This can be slow if it fails. *)
Ltac burn1
 := first
    [ burn0 
    | solve [firstorder burn0] ].

(* Try to factor the goal in some other way before applying
   one of the primitive tactics. *)
Ltac burn2
 := first
    [ burn1
    | f_equal; burn1 ].

(* Apply normalising rewrite rules in various combinations.
   We need to try different combinations. Simplifying can cause rewrite
   rules not to fire, or to not have the form required for a auto rule,
   so we want to try burn2 before and after rewrites. *)
Ltac burn3
 := first [ burn2
          | try rr; 
            first [ burn2
                  | try rs;
                    first [ burn2
                          | simpl; burn2 ]]].

(* Apply common factorings that should always make goals easier
   to solve. 

   Try to use injectivity between two constructor applications.
   These are common when we lookup values from the environment, 
    eg with  get ix tyenv = Some t1. *)
Ltac burn4
 := rip; match goal with 
      [ H1 : _ = ?C ?y1
      , H2 : _ = ?C ?y2 |- _]
      => assert (y1 = y2); rewrite H1 in H2; inverts H2; burn3

    | [ H1 : ?C ?y1 = _
      , H2 : ?C ?y2 = _ |- _]
      => assert (y1 = y2); rewrite H1 in H2; inverts H2; burn3

    | _ => burn3
 end.

(* Top-level megatactic.
   Try some simple, fast things first, then try everything. *)
Ltac burn 
 := first [burn0 | burn4].


(********************************************************************)
(* Assert a statement and prove it via burn.
   This leads to more structured proving than using plain 'assert', 
   because a 'have' form must always complete the goal. *)

Tactic Notation "have" constr(E) :=
 let H := fresh 
 in assert E as H by burn.

Tactic Notation "have" constr(E) "as" ident(H) :=
 assert E as H by burn.

Tactic Notation "have" constr(E) "by" tactic(T) :=
 let H := fresh 
 in assert E as H by T.

Tactic Notation "have" constr(E) "as" ident(H) "by" tactic(T) :=
 assert E as H by T.


(* Rewrite using burn.
   Just state the equality to use. *)
Tactic Notation "rrwrite" constr(xx)
 := let H := fresh 
    in assert xx as H by burn; rewrite H; clear H.

Tactic Notation "rrwrite" constr(xx) "in" hyp(H)
 := let H2 := fresh
    in  assert xx as H2 by burn; rewrite H2 in H; clear H2.

Tactic Notation "rw" constr(xx)             := rrwrite xx.
Tactic Notation "rw" constr(xx) "in" hyp(H) := rrwrite xx in H.




Require Export Iron.Data.List.
Require Export Iron.Data.Nat.
Require Export Iron.Norm.List.
Require Export Iron.Norm.
Require Export Iron.Tactics.Rip2.
Require Export Iron.Tactics.Rewrite2.
Require Export Iron.Tactics.Case.
Require Export Iron.Tactics.Nope.
Require Export Iron.Tactics.Break.
Require Export Iron.Tactics.Short.
Require Export Iron.Tactics.Comb.
Require Export Iron.Tactics.Have.
Require Export Iron.Tactics.LibTactics.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Logic.FunctionalExtensionality.


Tactic Notation "norm"
 := simpl in *; rip;
    repeat (norm_nat; norm_lists).


Tactic Notation "burn0"
 := norm; eauto; nope.

Tactic Notation "burn0" "using" tactic(T)
 := norm; eauto using T; nope.


Tactic Notation "burn"
 := try (solve [ burn0
               | red; burn0 ]).

Tactic Notation "burn" "using" tactic(T) 
 := try (solve [ burn0 using T
               | red; burn0 using T]).


Ltac have_auto ::= burn.


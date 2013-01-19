
Require Export Iron.Data.List.
Require Export Iron.Data.Nat.
Require Export Iron.Norm.List.
Require Export Iron.Norm.
Require Export Iron.Tactics.Rip2.
Require Export Iron.Tactics.Rewrite2.
Require Export Iron.Tactics.Case.
Require Export Iron.Tactics.Nope.
Require Export Iron.Tactics.Break.
Require Export Iron.Tactics.Rewrite.
Require Export Iron.Tactics.Have.
Require Export Iron.Tactics.Exists.
Require Export Iron.Tactics.Short.
Require Export Iron.Tactics.LibTactics.
Require Export Coq.Arith.EqNat.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Logic.FunctionalExtensionality.


Ltac norm
 := simpl in *; 
    repeat (rip; try norm_nat; try norm_lists).

Ltac tburn0 T
 := norm; eauto using T; nope.

Ltac tburn T
 := try (solve [ tburn0 T
               | red; tburn0 T]).

Tactic Notation "burn"
 := tburn false.

Tactic Notation "burn" "using" tactic(T) 
 := tburn T.

Ltac have_auto ::= burn.


Require Export Iron.Data.List.
Require Export Iron.Data.Nat.

Require Export Iron.Norm.List.
Require Export Iron.Norm.

Require Export Iron.Tactics.Rip2.
Require Export Iron.Tactics.Case.
Require Export Iron.Tactics.Nope.
Require Export Iron.Tactics.Break.
Require Export Iron.Tactics.Short.
Require Export Iron.Tactics.Comb.
Require Export Iron.Tactics.Down.
Require Export Iron.Tactics.Rewrite.
Require Export Iron.Tactics.LibTactics.

Require Export Coq.Arith.Compare_dec.
Require Import Coq.Logic.FunctionalExtensionality.

Tactic Notation "norm"
 := simpl in *;
    try (first [norm_nat | norm_lists]); eauto.

Tactic Notation "burn"
 := norm; eauto.
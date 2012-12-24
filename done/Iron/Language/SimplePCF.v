
(* Types, expressions, normal forms, values, lifting and substitution *)
Require Export Iron.Language.SimplePCF.Exp.

(* Typing judgement and environment weakening. *)
Require Export Iron.Language.SimplePCF.Ty.

(* Substitution of exps in exps preserves typing. *)
Require Export Iron.Language.SimplePCF.SubstExpExp.

(* Small step evaluation. *)
Require Export Iron.Language.SimplePCF.Step.

(* A well typed expression is either a value or can take a step. *)
Require Export Iron.Language.SimplePCF.Progress.

(* When an expression takes a step then the result has the same type. *)
Require Export Iron.Language.SimplePCF.Preservation.

(* Big step evaluation, and conversion between small step evaluation. *)
Require Export Iron.Language.SimplePCF.Eval.

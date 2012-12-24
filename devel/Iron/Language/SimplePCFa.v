
(* Types, expressions, normal forms, values, lifting and substitution *)
Require Export Iron.Language.SimplePCFa.Exp.
Require Export Iron.Language.SimplePCFa.ExpRefs.
Require Export Iron.Language.SimplePCFa.ExpLift.
Require Export Iron.Language.SimplePCFa.ExpLower.
Require Export Iron.Language.SimplePCFa.ExpSwap.
Require Export Iron.Language.SimplePCFa.ExpSubst.
Require Export Iron.Language.SimplePCFa.ExpSubsts.

(* Type Expressions *)
Require Export Iron.Language.SimplePCFa.Ty.

(* Type Judgement *)
Require Export Iron.Language.SimplePCFa.TyJudge.

(*
(* Substitution of exps in exps preserves typing. *)
Require Export Iron.Language.SimplePCF.SubstExpExp.
*)

(* Small step evaluation. *)
Require Export Iron.Language.SimplePCFa.StepBase.
Require Export Iron.Language.SimplePCFa.StepFrame.
Require Export Iron.Language.SimplePCFa.StepTerm.


(* Big step evaluation, and conversion between small step evaluation. *)
Require Export Iron.Language.SimplePCFa.Eval.

(* CIU equivalence *)
(* Require Export Iron.Language.SimplePCFa.EquivCIU. *)

(*
(* A well typed expression is either a value or can take a step. *)
Require Export Iron.Language.SimplePCF.Progress.

(* When an expression takes a step then the result has the same type. *)
Require Export Iron.Language.SimplePCF.Preservation.
*)

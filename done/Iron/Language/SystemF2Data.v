(* System-F2 with Algebraic Data Types *)

(********************************************************************)
(* Shared with SystemF2 *)

(* Kinds and kind environemnts. *)
Require Export Iron.Language.SystemF2.Ki.

(* Types, well formed and closed, lifting and substitution lemmas. *)
Require Export Iron.Language.SystemF2.Ty.

(* Kinds of types, weakening the kind environment. *)
Require Export Iron.Language.SystemF2.KiJudge.

(* Type environments, lifting and substitution lemmas. *)
Require Export Iron.Language.SystemF2.TyEnv.

(* Substitution of types in types preserves kinding. *)
Require Export Iron.Language.SystemF2.SubstTypeType.


(********************************************************************)
Require Export Iron.Language.SystemF2Data.Def.

(* Expressions and induction principle *)
Require Export Iron.Language.SystemF2Data.ExpBase.

(* Utils for working with case alternative *)
Require Export Iron.Language.SystemF2Data.ExpAlt.

(* Lifting and lifting lemmas for expressions *)
Require Export Iron.Language.SystemF2Data.ExpLift.

(* Substitution for expressions *)
Require Export Iron.Language.SystemF2Data.ExpSubst.

(* Expressions, normal forms, lifting and substitution. *)
Require Export Iron.Language.SystemF2Data.Exp.

(* Type Judgement. *)
Require Export Iron.Language.SystemF2Data.TyJudge.

(* Substitution of types in expressions preserves typing. *)
Require Export Iron.Language.SystemF2Data.SubstTypeExp.

(* Substitution of expressions in expressions preserves typing. *)
Require Export Iron.Language.SystemF2Data.SubstExpExp.

(* Small step evaluation contexts *)
Require Export Iron.Language.SystemF2Data.StepContext.

(* Small step evaluation. *)
Require Export Iron.Language.SystemF2Data.Step.

(* A well typed expression is either a value, or can take a step. *)
Require Export Iron.Language.SystemF2Data.Progress.

(* When an expression takes a step the results has the same type. *)
Require Export Iron.Language.SystemF2Data.Preservation.

(* Big step evaluation, and conversion to small steps. *)
Require Export Iron.Language.SystemF2Data.Eval.


(* System-F.
   Like STLC, but with type abstraction and application. *)

(* Kinds and kind environemnts. *)
Require Export Iron.Language.SystemF.Ki.

(* Types, well formed and closed, lifting and substitution lemmas. *)
Require Export Iron.Language.SystemF.Ty.

(* Type environments, lifting and substitution lemmas. *)
Require Export Iron.Language.SystemF.TyEnv.

(* Expressions, normal forms, lifting and substitution. *)
Require Export Iron.Language.SystemF.Exp.

(* Kinds of types, weakening the kind environment. *)
Require Export Iron.Language.SystemF.KiJudge.

(* Substitution of types in types preserves kinding. *)
Require Export Iron.Language.SystemF.SubstTypeType.

(* Type Judgement. *)
Require Export Iron.Language.SystemF.TyJudge.

(* Substitution of types in expressions preserves typing. *)
Require Export Iron.Language.SystemF.SubstTypeExp.

(* Substitution of expressions in expressions preserves typing. *)
Require Export Iron.Language.SystemF.SubstExpExp.

(* Small step evaluation. *)
Require Export Iron.Language.SystemF.Step.

(* A well typed expression is either a value, or can take a step. *)
Require Export Iron.Language.SystemF.Progress.

(* When an expression takes a step the results has the same type. *)
Require Export Iron.Language.SystemF.Preservation.

(* Big step evaluation, and conversion to small steps. *)
Require Export Iron.Language.SystemF.Eval.


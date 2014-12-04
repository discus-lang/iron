(* System-F2.
   Like System-F, but with type-type application. *)

(* Kinds and kind environemnts. *)
Require Export Iron.Language.SystemF2r.Ki.

(* Type expressions, and functions that operate on them *)
Require Export Iron.Language.SystemF2r.TyBase.

(* Lifting of indices in type expressions *)
Require Export Iron.Language.SystemF2r.TyLift.

(* Substitution of types in types, and lemmas about it *)
Require Export Iron.Language.SystemF2r.TySubst.

(* Simultaneous substitution of types in types, and lemmas about it *)
Require Export Iron.Language.SystemF2r.TySubsts.

(* Types, well formed and closed, lifting and substitution lemmas. *)
Require Export Iron.Language.SystemF2r.Ty.

(* Type environments, lifting and substitution lemmas. *)
Require Export Iron.Language.SystemF2r.TyEnv.

(* Expressions, normal forms, lifting and substitution. *)
Require Export Iron.Language.SystemF2r.Exp.

(* Kinds of types, weakening the kind environment. *)
Require Export Iron.Language.SystemF2r.KiJudge.

(* Substitution of types in types preserves kinding. *)
Require Export Iron.Language.SystemF2r.SubstTypeType.

(* Type Judgement. *)
Require Export Iron.Language.SystemF2r.TyJudge.

(* Substitution of types in expressions preserves typing. *)
Require Export Iron.Language.SystemF2r.SubstTypeExp.

(* Substitution of expressions in expressions preserves typing. *)
Require Export Iron.Language.SystemF2r.SubstExpExp.

(* Small step evaluation. *)
Require Export Iron.Language.SystemF2r.Step.

(* A well typed expression is either a value, or can take a step. *)
Require Export Iron.Language.SystemF2r.Progress.

(* When an expression takes a step the results has the same type. *)
Require Export Iron.Language.SystemF2r.Preservation.

(* Big step evaluation, and conversion to small steps. *)
Require Export Iron.Language.SystemF2r.Eval.


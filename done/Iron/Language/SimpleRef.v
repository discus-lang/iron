(* Simply Typed Lambda Calculus (STLC) 
   with Mutable References *)

(* Types, expressions, normal forms, values, lifting and substitution *)
Require Export Iron.Language.SimpleRef.Exp.

(* Typing judgement and environment weakening. *)
Require Export Iron.Language.SimpleRef.Ty.

(* Substitution of exps in exps preserves typing. *)
Require Export Iron.Language.SimpleRef.SubstExpExp.

(* Small step evaluation. *)
Require Export Iron.Language.SimpleRef.Step.

(* A well typed expression is either a value or can take a step. *)
Require Export Iron.Language.SimpleRef.Progress.

(* When an expression takes a step then the result has the same type. *)
Require Export Iron.Language.SimpleRef.Preservation.

(* Big step evaluation, and conversion between small step evaluation. *)
Require Export Iron.Language.SimpleRef.Eval.


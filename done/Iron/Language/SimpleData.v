
(* STLC with algebraic data types. *)

(* Types, well formed and closed, lifting and substitution lemmas. *)
Require Import Iron.Language.SimpleData.Ty.

(* Type definitions *)
Require Import Iron.Language.SimpleData.Def.

(* Expression structure *)
Require Import Iron.Language.SimpleData.ExpBase.

(* Lifting of debruijn indices in expressions. *)
Require Import Iron.Language.SimpleData.ExpLift.

(* Substitution for expressions. *)
Require Import Iron.Language.SimpleData.ExpSubst.

(* Functions and lemmas concerning case alternatives. *)
Require Import Iron.Language.SimpleData.ExpAlt.

(* Tie the above together, weak normal formes, closedX and value *)
Require Import Iron.Language.SimpleData.Exp.

(* Type judgement assigns a type to an expression. *)
Require Import Iron.Language.SimpleData.TyJudge.

(* Substitution of expressions in expressions preserves typing. *)
Require Import Iron.Language.SimpleData.SubstExpExp.

(* Evaluation contexts *)
Require Import Iron.Language.SimpleData.StepContext.

(* Lemmas for evaluation of case alternatives. *)
Require Import Iron.Language.SimpleData.StepAlt.

(* Single step evaluation rules *)
Require Import Iron.Language.SimpleData.Step.

(* A well typed expression is a value or can take a step*)
Require Import Iron.Language.SimpleData.Progress.

(* When an expression takes a step the result has the same type as before *)
Require Import Iron.Language.SimpleData.Preservation.

(* Big step evaluation and conversion between small steps *)
Require Import Iron.Language.SimpleData.Eval.


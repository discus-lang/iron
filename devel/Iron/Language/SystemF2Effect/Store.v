
Require Import Iron.Language.SystemF2Effect.KiJudge.
Require Import Iron.Language.SystemF2Effect.Ty.
Require Import Iron.Language.SystemF2Effect.TyJudge.
Require Import Iron.Language.SystemF2Effect.Va.
Require Export Iron.Language.SystemF2Effect.StoreBind.


(* A store is a list of store bindings. *)
Definition store := list sbind.


(* Store typing models the store.
   All types in the store typing have a corresponding binding in
   the store *)
Definition STOREM (se: stenv) (ss: store)
 := length se = length ss.
Hint Unfold STOREM.


(* Well typed store. *)
Definition STORET (se: stenv) (ss: store)
 := Forall2 (TYPEB nil nil se) ss se.
Hint Unfold STORET.


(* Well formed store. *)
Definition WfS (se: stenv) (ss: store)
 := Forall closedT se
 /\ STOREM se ss
 /\ STORET se ss.
Hint Unfold WfS.


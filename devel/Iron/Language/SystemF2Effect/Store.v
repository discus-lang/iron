
Require Import Iron.Language.SystemF2Effect.Type.KiJudge.
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.
Require Import Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(* A store is a list of store bindings. *)
Definition store := list stbind.


(* Store typing models the store.
   All types in the store typing have a corresponding binding in
   the store *)
Definition STOREM (se: stenv) (ss: store)
 := length se = length ss.
Hint Unfold STOREM.


(* Well typed store. *)
Definition STORET (se: stenv) (sp: stprops) (ss: store)
 := Forall2 (TYPEB nil nil se sp) ss se.
Hint Unfold STORET.


(* Well formed store. *)
Definition WfS (se: stenv) (sp: stprops) (ss: store)
 := Forall closedT se
 /\ STOREM se    ss
 /\ STORET se sp ss.
Hint Unfold WfS.


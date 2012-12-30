
Require Import Iron.Language.SystemF2Effect.Ty.
Require Import Iron.Language.SystemF2Effect.TyJudge.
Require Import Iron.Language.SystemF2Effect.VaExpBase.


(********************************************************************)
Definition store := list val.


(********************************************************************)
(* Store typing models the store.
   All types in the store typing have a corresponding binding in
   the store *)
Definition STOREM (se: stenv) (ss: store)
 := length se = length ss.
Hint Unfold STOREM.


(********************************************************************)
(* Well typed store. *)
Definition STORET (se: stenv) (ss: store)
 := Forall2 (TYPEV nil nil se) ss se.
Hint Unfold STORET.


(*******************************************************************)
(* Well formed store. *)
Definition WfS (se: stenv) (ss: list val)
 := Forall closedT se
 /\ STOREM se ss
 /\ STORET se ss.
Hint Unfold WfS.


(********************************************************************)
(* When we extend the store and store typing with a new binding, 
   then the resulting store is still well formed. *)
Lemma store_extended_wellformed
 :  forall se ss v t
 ,  WfS    se ss
 -> TYPEV  nil nil se v t
 -> WfS    (t <: se) (v <: ss).
Proof.
 admit.
Qed.

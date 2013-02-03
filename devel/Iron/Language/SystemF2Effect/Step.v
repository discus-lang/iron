
Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.Type.
Require Export Iron.Language.SystemF2Effect.Value.
Require Export Iron.Language.SystemF2Effect.Step.Pure.
Require Export Iron.Language.SystemF2Effect.Step.Frame.


(* A closed, well typed expression is either a value or can 
   take a step in the evaluation. *)
Theorem progress
 :  forall se sp ss x t e
 ,  WfS    se sp ss
 -> TYPEX  nil nil se sp x t e
 -> (exists v, x = XVal v) 
 \/ (exists ss' sp' x', STEPF ss fs x ss' fs' x').

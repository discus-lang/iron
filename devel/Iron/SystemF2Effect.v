(* System-F2. With region and effect types. *)

(* Kinds and kind environemnts. *)
Require Export Iron.SystemF2Effect.Kind.

(* Types and type environments. *)
Require Export Iron.SystemF2Effect.Type.

(* Values and computation expressions. *)
Require Export Iron.SystemF2Effect.Value.

(* Stores and store bindings. *)
Require Export Iron.SystemF2Effect.Store.

(* Evaluation *)
Require Export Iron.SystemF2Effect.Step.


(* - Do a single step and multi-step frame condition, 
     if the effect term does not contain write effects on 
     particular regions then all values in those regions are 
     preserved.
*)


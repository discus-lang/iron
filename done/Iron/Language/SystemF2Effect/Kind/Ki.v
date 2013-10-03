
Require Export Iron.Language.SystemF2Effect.Base.


(* Kinds *)
Inductive ki : Type :=
 (* Kind of data values. *)
 | KData   : ki              

 (* Kind of region variables and region handles. *)
 | KRegion : ki              

 (* Kind of effect types. *)
 | KEffect : ki

 (* Kind of type constructors. *)
 | KFun    : ki -> ki -> ki.

Hint Constructors ki.


(* Kind Environments *)
Definition kienv := list ki.
Hint Unfold kienv.

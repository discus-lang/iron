
Require Export Iron.SystemF2Effect.Base.


(* Kinds *)
Inductive ki : Type :=
 (* Kind of data objects that exist at runtime. *)
 | KData   : ki              

 (* Kind of region variables and region handles.
    Region types are used to separate the heap into disjoint set
    of locations. *)
 | KRegion : ki              

 (* Kind of effect types.
    Effect types are used to reason about potential interference
    of operators that modify the store. *)
 | KEffect : ki

 (* Kind of type constructors. *)
 | KFun    : ki -> ki -> ki.

Hint Constructors ki.


(* Kind Environments *)
Definition kienv := list ki.
Hint Unfold kienv.


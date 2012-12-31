
Require Export Iron.Language.SystemF2Effect.Value.


(* Store bindings are the primitive objects we keep in the store.
   Each one is tagged with the number of the region is in. *)
Inductive sbind :=
 | SBind : nat -> val -> sbind.
Hint Constructors sbind.


(* Types of store bindings. *)
Inductive TYPEB : kienv -> tyenv -> stenv -> sbind -> ty -> Prop := 
 | TbBind 
   :  forall ke te se n v t
   ,  TYPEV ke te se v t
   -> TYPEB ke te se (SBind n v) (tRef (TCon (TyConRegion n)) t).


Require Export Iron.Language.SystemF2Effect.Value.


(* Store bindings are the primitive objects we keep in the store.
   Each one is tagged with the number of the region is in. *)
Inductive sbind :=
 (* A region descriptor.
    One of these exists in the store for every live region. *)
 | SDesc  : sbind

 (* A store value in some region. *)
 | SValue : nat -> val -> sbind.

Hint Constructors sbind.


(* Types of store bindings. *)
Inductive TYPEB : kienv -> tyenv -> stenv -> sbind -> ty -> Prop := 
 | TbValue
   :  forall ke te se n v t
   ,  TYPEV ke te se v t
   -> TYPEB ke te se (SValue n v) (tRef (TCon (TyConRegion n)) t).

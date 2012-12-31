
Require Export Iron.Language.SystemF2Effect.Value.


(* Store bindings are the primitive objects we keep in the store.
   Each one is tagged with the number of the region is in. *)
Inductive stbind :=
 (* A store value in some region. *)
 | StValue : nat -> val -> stbind.

Hint Constructors stbind.


(* Types of store bindings. *)
Inductive TYPEB : kienv -> tyenv -> stenv -> stprops -> stbind -> ty -> Prop := 
 | TbValue
   :  forall ke te se sp n v t
   ,  TYPEV  ke te se sp v t
   -> TYPEB  ke te se sp (StValue n v) (tRef (TCon (TyConRegion n)) t).

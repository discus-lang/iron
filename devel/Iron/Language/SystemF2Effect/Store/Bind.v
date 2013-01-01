
Require Export Iron.Language.SystemF2Effect.Value.
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.WeakStProps.


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
Hint Constructors TYPEB.


(* Weakening store properties in store binding judegment *)
Lemma typeb_stprops_snoc
 :  forall ke te se sp v t p
 ,  TYPEB ke te se sp v t
 -> TYPEB ke te se (p <: sp) v t.
Proof. 
 intros. inverts H. eauto.
Qed.
Hint Resolve typeb_stprops_snoc.



Require Export Iron.SystemF2Effect.Value.
Require Export Iron.SystemF2Effect.Value.TyJudge.WeakStProps.
Require Export Iron.SystemF2Effect.Value.TyJudge.TypeKind.


(* Store bindings are the primitive objects we keep in the store.
   Each one is tagged with the number of the region is in. *)
Inductive stbind :=
 (* A store binding containing a live value. *)
 | StValue : nat -> val -> stbind

 (* A store binding that has been deallocated. *)
 | StDead  : nat -> stbind.
Hint Constructors stbind.


(* A store is a list of store bindings. *)
Definition store := list stbind.


Definition isStValue (b : stbind)
 := exists p v, b = StValue p v.
Hint Unfold isStValue.


Definition isStDead (b : stbind)
 := exists p,   b = StDead p.
Hint Unfold isStDead.


Definition regionOfStBind (b : stbind)
 := match b with 
    | StValue n _ => n
    | StDead  n   => n
    end.
Hint Unfold regionOfStBind.



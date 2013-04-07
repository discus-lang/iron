
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


(* Deallocate all store bindings in the given region by setting
   them to StDead. The dead bindings hold their locations in the
   store, but they no longer contain any value. *)
Fixpoint deallocate (p1 : nat) (b : stbind) {struct b} : stbind
 := match b with
    |  StValue p2 v
    => if beq_nat p1 p2
          then StDead  p2
          else StValue p2 v

    |  StDead p2
    => StDead p2 
    end.







Inductive stprop :=
 (* A region descriptor.
    One of these exists in the store for every live region in the store. *)
 | SRegion : nat -> stprop.


Definition stprops 
 := list stprop.

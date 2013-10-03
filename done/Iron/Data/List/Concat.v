
Require Import Iron.Data.List.Base.


Fixpoint catOptions {A} (xs : list (option A)) : list A
 := match xs with
    | nil             => nil
    | Some x :: rest  => x :: catOptions rest
    | None   :: rest  => catOptions rest
    end.


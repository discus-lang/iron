

(* Look for false hypothesis by inversion. *)
Ltac nope_1
 := match goal with
    (* Inverting an equality does not make progress, so clear it. *)
    | [H : _ |- _ = _ ] => clear H

    (* Keep inverting false hypothesis, provided doing so does not
       yield any more goals. *)
    | [H : _ |- _]
    => solve [inversion H]
    end.

Ltac nope
 := solve [repeat nope_1].



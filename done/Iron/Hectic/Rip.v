

(* Rip apart compound hypothesis and goals. *)
Ltac rip1
 := match goal with
    |- forall _, _      => intros
    | |- _ /\ _         => split
    | [H: _ /\ _ |- _]  => inversion H; clear H
    end.

Ltac rip
 := try (repeat rip1).


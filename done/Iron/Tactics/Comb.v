
Require Import Iron.Tactics.LibTactics.


Ltac comb 
 := match goal with 
      [ H1 : _ = ?C ?y1
      , H2 : _ = ?C ?y2 |- _]
      => assert (y1 = y2); rewrite H1 in H2; inverts H2; trivial

    | [ H1 : ?C ?y1 = _
      , H2 : ?C ?y2 = _ |- _]
      => assert (y1 = y2); rewrite H1 in H2; inverts H2; trivial
 end.

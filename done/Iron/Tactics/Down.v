

(* Apply matching rewrites from the hypothesis. *)
Ltac down 
 := match goal with
    | [H : ?X = _  |- ?X = _  ] => rewrite H
    | [H : _  = ?X |- ?X = _  ] => rewrite H
    | [H : ?X = _  |- _  = ?X ] => rewrite <- H
    | [H : _  = ?X |- _  = ?X ] => rewrite <- H
    end; auto.


(* Apply all rewrites from the hypothesis. *)
Ltac rewritess
 := match goal with
    | [H: eq _ _               |- _ ] => rewrite H
    | [H: forall _,     eq _ _ |- _ ] => rewrite H
    | [H: forall _ _,   eq _ _ |- _ ] => rewrite H
    | [H: forall _ _ _, eq _ _ |- _ ] => rewrite H
    end.


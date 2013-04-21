
Require Import Omega.

Tactic Notation "break" constr(E) :=
 let X := fresh "X" in remember (E) as X; destruct X.

Tactic Notation "breaka" constr(E) :=
 let X := fresh "X" in remember (E) as X; destruct X; auto.


(* Breaking up nat_compare
   Find the first (nat_compare ?E1 ?E2) and destruct it into the
   possible orderings. Also substitute ?E1 = ?E2 when they are equal. *)
Ltac fbreak_nat_compare :=
 match goal with 
 |  [ |- context [nat_compare ?E1 ?E2] ]
 => let X := fresh "X" 
    in  remember (nat_compare E1 E2) as X; destruct X;     

        (* In the equality case, sometimes we get equations like
           n = S n, which can't be substituted. Hence try subst. *)
        [ match goal with 
          |  [ H: Eq = nat_compare E1 E2 |- _ ] 
          => symmetry in H; apply nat_compare_eq in H; 
             try subst 
          end

        | match goal with 
          |  [ H: Lt = nat_compare E1 E2 |- _ ]
          => symmetry in H; apply nat_compare_lt in H
          end 

        | match goal with
          |  [ H: Gt = nat_compare E1 E2 |- _ ]
          => symmetry in H; apply nat_compare_gt in H
         end
        ]
 end.


(* New style ********************************************************)

Ltac split_nat_dec :=
  match goal with
  | [ H: context[le_gt_dec ?X ?Y] |- _]
  => case (le_gt_dec X Y); intro

  | [ |- context[le_gt_dec ?X ?Y] ]
  => case (le_gt_dec X Y); intro
  end.

Ltac split_dec
 := split_nat_dec.


Ltac split_if :=
  match goal with 
  | [ |- context[if ?X then _ else _] ]
    => let Z := fresh in remember X as Z; destruct Z

  | [ H: context[if ?X then _ else _] |- _ ]
    => let Z := fresh in remember X as Z; destruct Z
  end.


Ltac split_match_option :=
  match goal with 
  | [ |- context [match ?X with | Some _ => _ | None => _ end] ] 
    => let Z := fresh in remember X as Z; destruct Z

  | [ H: context [match ?X with | Some _ => _ | None => _ end] |- _]
    => let Z := fresh in remember X as Z; destruct Z
  end.


Ltac split_match_comparison :=
  match goal with
  | [ |- context [match ?X with | Eq => _ | Lt => _ | Gt => _ end] ] 
    => let Z := fresh in remember X as Z; destruct Z

  | [ H: context [match ?X with | Eq => _ | Lt => _ | Gt => _ end] |- _]
    => let Z := fresh in remember X as Z; destruct Z
  end.


Ltac split_match_nat :=
  match goal with
  | [ |- context [match ?X with | 0 => _ | S _ => _ end] ]
    => let Z := fresh in remember X as Z; destruct Z

  | [ H: context [match ?X with | 0 => _ | S _ => _ end] |- _]
    => let Z := fresh in remember X as Z; destruct Z
  end.


Ltac split_match
 := first [ split_dec
          | split_if 
          | split_match_option 
          | split_match_comparison
          | split_match_nat ].



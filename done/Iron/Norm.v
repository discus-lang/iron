
Require Import Iron.Norm.List.
Require Import Iron.Data.List.
Require Import Iron.Data.Nat.
Require Import Iron.Tactics.


(********************************************************************)
(* Tactic to help deal with lifting functions *)
Ltac fbreak_get 
 := match goal with 
     |  [ |- context [get ?E1 ?E2] ] 
     => let X := fresh 
        in remember (get E1 E2) as X; destruct X
    end.


Ltac fbreak_le_gt_dec
 := match goal with 
     |  [ |- context [le_gt_dec ?n ?n'] ]
     => case (le_gt_dec n n'); intros
    end.


Ltac lift_cases := 
 repeat (intros;
  first [ fbreak_nat_compare
        | fbreak_le_gt_dec
        | fbreak_get]); intros.


Ltac lift_burn t
 := induction t; intros; eauto;  

          (* this gets most var cases *)
    first [ repeat (simpl; lift_cases; try norm_nat; intros); burn 
      
          (* try to apply rewrites from the hypotheses *)    
          | repeat rewritess ].


Ltac norm_inverts_option := 
 match goal with 
 | [H : Some _ = Some _ |- _] => inverts H
 | [H : Some _ = None   |- _] => inverts H
 | [H : None   = Some _ |- _] => inverts H
 end.


Ltac norm_beq_nat
 := match goal with 
    |  [ H : true = beq_nat ?X ?Y |- _ ] 
    => symmetry in H; apply beq_nat_true in H

    |  [ H : beq_nat ?X ?Y = true |- _ ] 
    => apply beq_nat_true in H

    |  [ H : false = beq_nat ?X ?Y |- _ ] 
    => symmetry in H; apply beq_nat_false in H

    |  [ H : beq_nat ?X ?Y = false |- _ ] 
    => apply beq_nat_false in H
    end.


Ltac norm_nat_compare :=
  match goal with 
  (* Equality *)
  | [ H: nat_compare _ _ = Eq           |- _ ]
    => apply nat_compare_eq in H

  | [ H: Eq = nat_compare _ _           |- _ ]
    => symmetry in H; apply nat_compare_eq in H

  | [ H: context [nat_compare _ _ = Eq] |- _ ]
    => rewrite <- nat_compare_eq in H

  | [ H: context [Eq = nat_compare _ _] |- _ ]
    => symmetry in H; rewrite <- nat_compare_eq in H


  (* Less Than *)
  | [ H: nat_compare _ _ = Lt           |- _ ]
    => apply nat_compare_lt in H

  | [ H: Lt = nat_compare _ _           |- _ ]
    => symmetry in H; apply nat_compare_lt in H

  | [ H: context [Lt = nat_compare _ _] |- _ ]
    => symmetry in H; rewrite <- nat_compare_lt in H

  | [ H: context [nat_compare _ _ = Lt] |- _ ]
    => rewrite <- nat_compare_lt in H


  (* Greather Than *)
  | [ H: nat_compare _ _ = Gt           |- _ ]
    => apply nat_compare_gt in H

  | [ H: Gt = nat_compare _ _           |- _ ]
    => symmetry in H; apply nat_compare_gt in H

  | [ H: context [Gt = nat_compare _ _] |- _ ]
    => symmetry in H; rewrite <- nat_compare_gt in H

  | [ H: context [nat_compare _ _ = Gt] |- _ ]
    => rewrite <- nat_compare_gt in H
  end.


Tactic Notation "nnat"    := norm_nat.
Tactic Notation "nforall" := norm_lists.


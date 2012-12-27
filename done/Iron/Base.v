
Require Export Iron.Data.List.
Require Export Iron.Data.Nat.
Require Export Iron.Tactics.
Require Export Coq.Program.Basics.


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
    first [ repeat (simpl; lift_cases; nnat; intros); burn 
      
          (* try to apply rewrites from the hypotheses *)    
          | repeat rewritess ].


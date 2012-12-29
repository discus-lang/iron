
Require Import Iron.Language.SimplePCF.Step.
Require Import Iron.Language.SimplePCF.Ty.
Require Import Iron.Language.SimplePCF.SubstExpExp.


(* If a closed, well typed expression takes an evaluation step
   then the result has the same type as before. *)
Theorem preservation
 :  forall x x' t
 ,  TYPE nil x  t
 -> STEP  x x'
 -> TYPE nil x' t.
Proof.
 intros x x' t HT HS. gen t.
 induction HS; rip; try (inverts HT; progress burn).

 Case "EsContext".
  destruct H; inverts HT; burn.

 Case "EsLamApp".
  inverts HT. inverts H3.
  burn using subst_exp_exp.

 Case "EsFix".
  inverts HT.
  burn using subst_exp_exp.
Qed.


(* When we multi-step evaluate some expression,
   then the result has the same type as the before. *)
Lemma preservation_steps
 :  forall x1 t1 x2
 ,  TYPE nil x1 t1
 -> STEPS    x1 x2
 -> TYPE nil x2 t1.
Proof.
 intros x1 t1 x2 HT HS.
 induction HS; burn using preservation.
Qed.


(* When we multi-step evaluate some expression, 
   then the result has the same type as the original.
   Using the left-linearised form for the evaluation. *)
Lemma preservation_stepsl
 :  forall x1 t1 x2
 ,  TYPE nil x1 t1
 -> STEPSL   x1 x2
 -> TYPE nil x2 t1.
Proof.
 intros x1 t1 x2 HT HS.
 induction HS; burn using preservation.
Qed.


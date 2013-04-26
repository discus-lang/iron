
Require Import Iron.Language.SystemF2Data.Base.


(********************************************************************)
(* Data Constructors
   Carries a data constructor tag and an arity. *)
Inductive datacon : Type :=
 | DataCon    : nat -> nat -> datacon.
Hint Constructors datacon.


(* The unit data constructor. *)
Definition dcUnit := DataCon   0 0. 
Hint Unfold dcUnit.


(********************************************************************)
Fixpoint datacon_beq t1 t2 :=
  match t1, t2 with
  | DataCon n11 n12, DataCon n21 n22 
  => beq_nat n11 n21 && beq_nat n12 n22
  end.


(* Boolean equality for data constructors. *)
Lemma datacon_beq_eq
 :  forall dc dc' 
 ,  true = datacon_beq dc dc'
 -> dc = dc'.
Proof.
 intros.
 destruct dc.
 destruct dc'.
 snorm.
Qed.


(* Boolean negation for data constructors. *)
Lemma datacon_beq_false
 :  forall dc 
 ,  false = datacon_beq dc dc 
 -> False.
Proof.
 intro.
 destruct dc.
 snorm.
 inverts H.
  induction n.  false. auto.
  induction n0. false. auto.
Qed.



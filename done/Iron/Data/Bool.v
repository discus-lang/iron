
Require Export Coq.Bool.Bool.


Lemma negb_true_elim
 :  forall x
 ,  true   = negb x
 -> false  = x.
Proof. destruct x; auto. Qed.


Lemma negb_true_intro
 :  forall x
 ,  false = x
 -> true  = negb x .
Proof. destruct x; eauto. Qed.

Lemma negb_false_elim
 :  forall x
 ,  false  = negb x
 -> true   = x.
Proof. destruct x; auto. Qed.


Ltac norm_negb
 := match goal with 
    | [H : true  = negb _ |- _ ]
    => apply negb_true_elim in H

    | [H : false = negb _ |- _ ]
    => apply negb_false_elim in H
    end.


(********************************************************************)
Lemma beq_true_split
 :  forall A B
 ,  true = andb A B
 -> true = A /\ true = B.
Proof.
 intros.
 destruct A. 
  tauto.
  simpl in H. congruence.
Qed.
Hint Resolve beq_true_split.


Lemma beq_false_split
 :  forall A B
 ,  false = andb A B
 -> false = A \/ false = B.
Proof.
 intros.
 destruct A.
  simpl in H. subst. tauto.
  tauto.
Qed.
Hint Resolve beq_false_split.


Lemma beq_false_join
 :  forall A B
 ,  false = A \/ false = B
 -> false = andb A B.
Proof.
 intros.
 inversion H. subst.
 tauto.
 destruct A; tauto.
Qed.
Hint Resolve beq_false_split.


Ltac norm_andb
 := match goal with 
    | [H : true  = andb _ _ |- _]
    => apply beq_true_split in H

    | [H : andb _ _ = true |- _]
    => symmetry in H; apply beq_true_split in H

    | [H : false = andb _ _ |- _]
    => apply beq_false_split in H

    | [H : andb _ _ = false |- _]
    => symmetry in H; apply beq_false_split in H
    end.


(********************************************************************)
Ltac norm_orb
 := match goal with
    | [H : true    = orb _ _ |- _]
    => symmetry in H; apply orb_true_iff in H

    | [H : orb _ _ = true    |- _]
    => apply orb_true_iff in H

    | [H : false   = orb _ _ |- _]
    => symmetry in H; apply orb_false_iff in H

    | [H : orb _ _ = false   |- _]
    => apply orb_false_iff in H
    end.


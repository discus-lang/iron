

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



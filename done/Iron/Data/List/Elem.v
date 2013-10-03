
Require Import Iron.Data.List.Base.


(* Check if any element in a list matches the given predicate. *)
Fixpoint elem {A} (p : A -> bool) (xx : list A)
 := match xx with
    | nil      => false
    | x :: xs  => if p x then true else elem p xs
    end.


Lemma elem_get_not
 :  forall {A} (p : A -> bool) (xx : list A) 
 ,  not (exists ix x, get ix xx = Some x /\ p x = true)
 -> elem p xx = false.
Proof. 
 intros.
 induction xx.
 - simpl. auto.
 - remember (p a) as X.
   destruct X.
   + simpl. 
     rewrite <- HeqX.
     assert (exists ix x, get ix (xx :> a) = Some x /\ p x = true).
      exists 0. exists a. intuition.
     tauto.
     
   + simpl. 
     rewrite <- HeqX. 
     eapply IHxx.
     unfold not. 
     intros.
     destruct H0 as [ix].
     destruct H0 as [x].
     inversion H0.
     assert (get (S ix) (xx :> a) = Some x).
      simpl. auto.
     assert (exists ix x, get ix (xx :> a) = Some x /\ p x = true).
      exists (S ix). exists x. auto.
     tauto.
Qed.  


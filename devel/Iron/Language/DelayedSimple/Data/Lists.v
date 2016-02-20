
Require Export Coq.Lists.List.
Require Export Iron.Language.DelayedSimple.Tactics.Chargueraud.


(********************************************************************)
(* Forall Lemmas *)

Lemma Forall_inst
 :  forall {A B} a' xs (P: A -> B -> Prop)
 ,  Forall (fun x => forall a, P a x) xs
 -> Forall (fun x => P a' x) xs.
Proof.
 intros.
 induction xs.
 - auto.
 - eapply Forall_cons.
   + inverts H. eapply H2.
   + inverts H. eapply IHxs. assumption.
Qed.


Lemma Forall_mp
 :  forall {A} (P Q: A -> Prop)  xs
 ,  Forall (fun x => P x -> Q x) xs
 -> Forall (fun x => P x)        xs
 -> Forall (fun x => Q x)        xs.
Proof.
 intros.
 induction xs.
 - auto.
 - eapply Forall_cons.
   + inverts H. inverts H0. auto.
   + inverts H. inverts H0. auto.
Qed. 


Lemma Forall_mp_const 
 :  forall {A} P (Q: A -> Prop)  xs
 ,  P
 -> Forall (fun x => P -> Q x) xs
 -> Forall (fun x => Q x)      xs.
Proof.
 intros.
 induction H.
 - auto.
 - apply Forall_cons.
   + auto.
   + auto.
Qed.


Lemma Forall_map
 :  forall {A B}
    (P: B -> Prop) (f: A -> B) (xs: list A)
 ,  Forall (fun x => P (f x)) xs
 -> Forall P (map f xs).
Proof.
 intros. induction xs.
  apply Forall_nil.
  inverts H. simpl. intuition.
Qed.


(********************************************************************)
(* Forall2 Lemmas *)

Lemma Forall2_mp
 :  forall {A B} (P Q: A -> B -> Prop)  aa bb
 ,  Forall2 (fun a b => P a b -> Q a b) aa bb
 -> Forall2 (fun a b => P a b)          aa bb
 -> Forall2 (fun a b => Q a b)          aa bb.
Proof.
 intros.
 induction H0.
 - auto.
 - inverts H.
   apply Forall2_cons; auto.
Qed.


Lemma Forall2_map
 :  forall {A B C D}
    (P:  B -> D -> Prop) (f:  A -> B) (g:  C -> D) 
    (xs: list A) (ys: list C)
 ,  Forall2 (fun x y => P (f x) (g y)) xs ys
 -> Forall2 P (map f xs) (map g ys).
Proof.
 intros.
 induction H.
 - simpl. auto.
 - simpl. apply Forall2_cons; auto. 
Qed.


Lemma Forall2_map'
 :  forall {A B C D}
    (P: B -> D -> Prop) (f:  A -> B) (g:  C -> D)
    (xs: list A) (ys: list C)
 ,  Forall2 P (map f xs) (map g ys)
 -> Forall2 (fun x y => P (f x) (g y)) xs ys.
Proof.
 intros. gen ys.
 induction xs; intros.
  induction ys; intros.
   auto.
   inverts H.
   destruct ys.
    inverts H.
    simpl in H.
    inverts H. eauto.
Qed.


(********************************************************************)
(* Convert Forall to Forall2 *)
Lemma Forall_Forall2_right
 :  forall  {A B C} 
    (P: B -> C -> Prop) 
    (f: A -> B) (g: A -> C) (aa: list A)
 ,  Forall  (fun b => forall c, P b c) (map f aa)
 -> Forall2 P (map f aa) (map g aa).
Proof.
 intros.
 induction aa.
 - simpl. auto.
 - simpl in *.
   inverts H.
   apply Forall2_cons.
   auto. auto.
Qed.



Require Export Iron.Language.SystemF2Effect.Step.Frame.


(********************************************************************)
(* Region identifier is not mentioned some FPriv frame. *)
Fixpoint NoPrivF (p : nat) (f : frame) {struct f} :=
 match f with
 | FLet t x               => True
 | FPriv None p1          => ~(p = p1)
 | FPriv (Some p1) p2     => ~(p = p1) /\ ~(p = p2)
 end.

Definition NoPrivFs (p : nat) (fs : stack)
 := Forall (NoPrivF p) fs.


Lemma noprivFs_head 
 :  forall p fs f
 ,  NoPrivFs p (fs :> f)
 -> NoPrivF  p f. 
Proof.
 intros. inverts H. eauto.
Qed.
Hint Resolve noprivFs_head.


Lemma noprivFs_tail
 :  forall p fs f
 ,  NoPrivFs p (fs :> f)
 -> NoPrivFs p fs. 
Proof.
 intros. inverts H. eauto.
Qed.
Hint Resolve noprivFs_tail.


(********************************************************************)
(* Region identifier is not mentioned in the given stack frame. *)
Fixpoint FreshF (p : nat) (ff : frame) {struct ff} :=
 match ff with
 | FLet  t x           => FreshT p t /\ FreshX p x
 | FPriv None      p2  => ~(p = p2)
 | FPriv (Some p1) p2  => ~(p = p1)  /\ ~(p = p2)
 end.


(* Region identifier is not mentioned in the given stack.  *)
Definition FreshFs (p : nat) (fs : stack) 
 := Forall (FreshF p) fs.
Hint Unfold FreshFs.


Lemma freshFs_head 
 :  forall p f fs
 ,  FreshFs p (fs :> f)
 -> FreshFs p fs.
Proof. intros. inverts H. eauto. Qed.
Hint Resolve freshFs_head.


Lemma freshFs_tail
 :  forall p f fs
 ,  FreshFs p (fs :> f)
 -> FreshF  p f.
Proof. intros. inverts H. eauto. Qed.
Hint Resolve freshFs_tail.


Lemma freshFs_cons
 :  forall p f fs
 ,  FreshFs p fs -> FreshF p f
 -> FreshFs p (fs :> f).
Proof. snorm. Qed.
Hint Resolve freshFs_cons.


Lemma freshF_noprivF
 : forall p f
 , FreshF p f -> NoPrivF p f.
Proof.
 intros.
 destruct f.
 - snorm.
 - destruct o; snorm.
Qed.
Hint Resolve freshF_noprivF. 


Lemma freshFs_noprivFs
 : forall  p fs
 , FreshFs p fs -> NoPrivFs p fs.
Proof.
 intros.
 induction fs.
 - unfold NoPrivFs. eauto.
 - unfold NoPrivFs. inverts H. firstorder.
Qed.
Hint Resolve freshFs_noprivFs.


(*********************************************************************)
(* Region identifier is not mentioned in the types of the free variables
   of the given stack frame. *)
Fixpoint   FreshFreeF (p : nat) (te : tyenv) (f : frame) {struct f} :=
 match f with
 | FLet t x       => FreshFreeX p (te :> t) x
 | FPriv _ _      => True
 end.


(* Region identifier is not mentioned in the types of the free variables
   of the given stack. *)
Definition FreshFreeFs (p : nat) (te : tyenv) (fs : stack)
 := Forall (FreshFreeF p te) fs.
Hint Unfold FreshFreeFs.


Lemma freshFreeF_nil
 :  forall p f
 ,  FreshF p f
 -> FreshFreeF p nil f.
Proof.
 intros.
 destruct f; snorm.
Qed.
Hint Resolve freshFreeF_nil.


Lemma freshFreeFs_nil
 :  forall p fs
 ,  FreshFs p fs
 -> FreshFreeFs p nil fs.
Proof.
 intros.
 induction fs; eauto.
 inverts H. rip.
Qed.
Hint Resolve freshFreeFs_nil.


Lemma freshFreeFs_tail
 :  forall p te fs f
 ,  FreshFreeFs p te (fs :> f)
 -> FreshFreeFs p te fs.
Proof.
 intros.
 inverts H. auto.
Qed.
Hint Resolve freshFreeFs_tail.


(********************************************************************)
(* Region identifier is not mentioned in the types of the locations
   used in the given stack frame. *)
Fixpoint  FreshSuppF   (p : nat) (se : stenv) (f : frame) {struct f} :=
 match f with
 | FLet  t x      => FreshSuppX p se x
 | FPriv _ _      => True
 end.


(* Region identifier is not mentioned in the types of the locations
   used in the given stack. *)
Definition FreshSuppFs p2 se fs 
 := Forall (FreshSuppF p2 se) fs.
Hint Unfold FreshSuppFs.


Lemma freshSuppFs_tail
 :  forall p te fs f
 ,  FreshSuppFs p te (fs :> f)
 -> FreshSuppFs p te fs.
Proof.
 intros.
 inverts H. auto.
Qed.
Hint Resolve freshSuppFs_tail.


Lemma freshSuppFs_head
 :  forall p te fs f
 ,  FreshSuppFs p te (fs :> f)
 -> FreshSuppF  p te f.
Proof.
 intros.
 inverts H. auto.
Qed.
Hint Resolve freshSuppFs_head.


Lemma freshSuppF_mergeTE
 :  forall p1 p2 p3 te f
 ,  FreshSuppF p1 te f
 -> FreshSuppF p2 te f
 -> FreshSuppF p2 (mergeTE p3 p1 te) f.
Proof.
 intros.
 destruct f.
 - snorm.
   eapply freshSuppX_mergeTE; auto.
 - eauto. 
Qed.


Lemma freshSuppFs_mergeTE
 :  forall p1 p2 p3 te fs
 ,  FreshSuppFs p1 te fs
 -> FreshSuppFs p2 te fs
 -> FreshSuppFs p2 (mergeTE p3 p1 te) fs.
Proof.
 intros.
 unfold FreshSuppFs in *.
 induction fs; auto.
 inverts H.
 inverts H0. rip.
 eapply Forall_cons; auto.
 eapply freshSuppF_mergeTE; auto.
Qed.


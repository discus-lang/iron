
Require Export Iron.Language.SystemF2Effect.Step.Frame.


(********************************************************************)
(* Region identifier is not mentioned in the given stack frame. *)
Fixpoint freshF (p : nat) (ff : frame) {struct ff} 
 := match ff with
    | FLet  t x           => freshT p t /\ freshX p x
    | FPriv None      p2  => beq_nat p p2 = false
    | FPriv (Some p1) p2  => beq_nat p p1 = false /\ beq_nat p p2 = false
    end.


(* Region identifier is not mentioned in the given stack.  *)
Definition freshFs (p : nat) (fs : stack) 
 := Forall (freshF p) fs.
Hint Unfold freshFs.


(* Region identifier is not mentioned in the types of the free variables
   of the given stack frame. *)
Fixpoint   freshFreeF (p : nat) (te : tyenv) (f : frame) {struct f}
 := match f with
    | FLet t x       => freshFreeX p (te :> t) x
    | FPriv _ _      => True
    end.


(* Region identifier is not mentioned in the types of the free variables
   of the given stack. *)
Definition freshFreeFs (p : nat) (te : tyenv) (fs : stack)
 := Forall (freshFreeF p te) fs.
Hint Unfold freshFreeFs.


(* Region identifier is not mentioned in the types of the locations
   used in the given stack frame. *)
Fixpoint  freshSuppF   (p : nat) (se : stenv) (f : frame) {struct f}
 := match f with
    | FLet  t x      => freshSuppX p se x
    | FPriv _ _      => True
    end.

(* Region identifier is not mentioned in the types of the locations
   used in the given stack. *)
Definition freshSuppFs p2 se fs 
 := Forall (freshSuppF p2 se) fs.
Hint Unfold freshSuppFs.


(********************************************************************)
Lemma freshFs_head 
 :  forall p f fs
 ,  freshFs p (fs :> f)
 -> freshFs p fs.
Proof. intros. inverts H. eauto. Qed.
Hint Resolve freshFs_head.


Lemma freshFs_tail
 :  forall p f fs
 ,  freshFs p (fs :> f)
 -> freshF  p f.
Proof. intros. inverts H. eauto. Qed.
Hint Resolve freshFs_tail.


Lemma freshFs_cons
 :  forall p f fs
 ,  freshFs p fs -> freshF p f
 -> freshFs p (fs :> f).
Proof. snorm. Qed.
Hint Resolve freshFs_cons.


(********************************************************************)
Lemma freshFreeF_nil
 :  forall p f
 ,  freshF p f
 -> freshFreeF p nil f.
Proof.
 intros.
 destruct f; snorm.
Qed.
Hint Resolve freshFreeF_nil.


Lemma freshFreeFs_nil
 :  forall p fs
 ,  freshFs p fs
 -> freshFreeFs p nil fs.
Proof.
 intros.
 induction fs; eauto.
 inverts H. rip.
Qed.
Hint Resolve freshFreeFs_nil.


Lemma freshFreeFs_tail
 :  forall p te fs f
 ,  freshFreeFs p te (fs :> f)
 -> freshFreeFs p te fs.
Proof.
 intros.
 inverts H. auto.
Qed.
Hint Resolve freshFreeFs_tail.


(********************************************************************)
Lemma freshSuppFs_tail
 :  forall p te fs f
 ,  freshSuppFs p te (fs :> f)
 -> freshSuppFs p te fs.
Proof.
 intros.
 inverts H. auto.
Qed.
Hint Resolve freshSuppFs_tail.


Lemma freshSuppFs_head
 :  forall p te fs f
 ,  freshSuppFs p te (fs :> f)
 -> freshSuppF  p te f.
Proof.
 intros.
 inverts H. auto.
Qed.
Hint Resolve freshSuppFs_head.


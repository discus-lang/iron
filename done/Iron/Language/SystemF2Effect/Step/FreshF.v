
Require Export Iron.Language.SystemF2Effect.Step.Frame.


(********************************************************************)
Fixpoint freshF (p : nat) (ff : frame) {struct ff} : Prop := 
 match ff with
 | FLet  t x     => freshT p t /\ freshX p x
 | FPriv p1      => beq_nat p p1 = false
 | FExt  p1 p2   => beq_nat p p1 = false /\ beq_nat p p2 = false
 end.


Definition freshFs (p : nat) (fs : stack) : Prop
 := Forall (freshF p) fs.
Hint Unfold freshFs.


Fixpoint   freshFreeF p2 te f {struct f} :=
 match f with
 | FLet t x        => freshFreeX p2 te x
 | FPriv _         => True
 | FExt  _ _       => True
 end.

Definition freshFreeFs p2 te fs 
 := Forall (freshFreeF p2 te) fs.
Hint Unfold freshFreeFs.


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


Lemma freshFreeF_nil
 : forall p f
 , freshFreeF p nil f.
Proof. 
 intros.
 destruct f; snorm.
Qed.
Hint Resolve freshFreeF_nil.


Lemma freshFreeFs_nil
 : forall p fs
 , freshFreeFs p nil fs.
Proof.
 intros.
 induction fs; auto.
Qed.
Hint Resolve freshFreeFs_nil.



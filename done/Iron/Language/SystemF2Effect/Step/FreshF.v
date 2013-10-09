
Require Export Iron.Language.SystemF2Effect.Step.Frame.


Fixpoint freshF (p : nat) (ff : frame) {struct ff} : Prop := 
 match ff with
 | FLet  t x     => freshT p t /\ freshX p x
 | FPriv p1      => beq_nat p p1 = false
 | FExt  p1 p2   => beq_nat p p1 = false /\ beq_nat p p2 = false
 end.


Definition freshFs (p : nat) (fs : stack) : Prop
 := Forall (freshF p) fs.
Hint Unfold freshFs.


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
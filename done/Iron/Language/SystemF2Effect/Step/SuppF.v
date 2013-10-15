
Require Export Iron.Language.SystemF2Effect.Step.FreshF.


(* Store location is mentioned in (supports) the given frame. *)
Fixpoint suppF  (l : nat) (f : frame) {struct f} := 
 match f with
 | FLet t x   => suppX l x
 | FPriv _ _  => False
 end.

(* Store location is mentioned in (supports) the given stack. *)
Definition suppFs (l : nat) (fs : stack) 
 := exists f, In f fs /\ suppF l f.


(* Store environment covers all locations mentioned in the given frame.
   Alternatively: all locations in the given frame point to valid
   entries in the store environment, *)
Definition coversF  (se : stenv) (f  : frame)
 := forall l, suppF l f -> (exists t, get l se = Some t).
Hint Unfold coversF.


(* Store environment covers all locations mentioned in the given stack. *)
Definition coversFs (se : stenv) (fs : stack)
 := Forall (coversF se) fs.
Hint Unfold coversFs.


(********************************************************************)
Lemma coversFs_head
 :  forall se fs f
 ,  coversFs se (fs :> f)
 -> coversF  se f.
Proof.
 intros.
 unfold coversFs in *.
 inverts H. auto.
Qed.
Hint Resolve coversFs_head.


Lemma coversFs_tail
 :  forall se fs f
 ,  coversFs se (fs :> f)
 -> coversFs se fs.
Proof.
 intros.
 unfold coversFs in *.
 inverts H. auto.
Qed.
Hint Resolve coversFs_tail.


Lemma freshSuppF_coversF
 :  forall p se f t
 ,  coversF se f
 -> freshSuppF p se f
 -> freshSuppF p (t <: se) f.
Proof.
 intros.
 unfold coversF in *.
 destruct f.
 - snorm.
   unfold freshSuppX in *.
   rip.
   lets D: H H2. 
   destruct D as [t']. 

   assert (t1 = t').
    eapply get_snoc_some 
     with (x2 := t) in H3.
    rewrite H1 in H3. inverts H3.
   eauto. subst.
   eauto.

 - eauto.
Qed.


Lemma freshSuppFs_coveredFs
 :  forall p se fs t
 ,  coversFs se fs
 -> freshSuppFs p se fs
 -> freshSuppFs p (t <: se) fs.
Proof.
 intros. 

 induction fs as [|f].
 - snorm.
 - have (coversF  se f).
   have (coversFs se fs).
   have (freshSuppFs p se fs).
   have (freshSuppF  p se f).
   rip.
    
   unfold freshSuppFs.
   eapply Forall_cons; auto.
   
   eapply freshSuppF_coversF; auto.
Qed.


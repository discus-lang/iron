
Require Export Iron.Language.SystemF2Effect.Step.FreshF.


(* Store location is mentioned in (supports) the given frame. *)
Fixpoint SuppF  (l : nat) (f : frame) {struct f} := 
 match f with
 | FLet t x   => SuppX l x
 | FPriv _ _  => False
 end.

(* Store location is mentioned in (supports) the given stack. *)
Definition SuppFs (l : nat) (fs : stack) 
 := exists f, In f fs /\ SuppF l f.


(* Store environment covers all locations mentioned in the given frame.
   Alternatively: all locations in the given frame point to valid
   entries in the store environment, *)
Definition CoversF  (se : stenv) (f  : frame)
 := forall l, SuppF l f -> (exists t, get l se = Some t).
Hint Unfold CoversF.


(* Store environment covers all locations mentioned in the given stack. *)
Definition CoversFs (se : stenv) (fs : stack)
 := Forall (CoversF se) fs.
Hint Unfold CoversFs.


(********************************************************************)
Lemma coversFs_head
 :  forall se fs f
 ,  CoversFs se (fs :> f)
 -> CoversF  se f.
Proof.
 intros.
 unfold CoversFs in *.
 inverts H. auto.
Qed.
Hint Resolve coversFs_head.


Lemma coversFs_tail
 :  forall se fs f
 ,  CoversFs se (fs :> f)
 -> CoversFs se fs.
Proof.
 intros.
 unfold CoversFs in *.
 inverts H. auto.
Qed.
Hint Resolve coversFs_tail.


Lemma freshSuppF_coversF
 :  forall p se f t
 ,  CoversF se f
 -> FreshSuppF p se f
 -> FreshSuppF p (t <: se) f.
Proof.
 intros.
 unfold CoversF in *.
 destruct f.
 - snorm.
   unfold FreshSuppX in *.
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
 ,  CoversFs se fs
 -> FreshSuppFs p se fs
 -> FreshSuppFs p (t <: se) fs.
Proof.
 intros. 

 induction fs as [|f].
 - snorm.
 - have (CoversF  se f).
   have (CoversFs se fs).
   have (FreshSuppFs p se fs).
   have (FreshSuppF  p se f).
   rip.
    
   unfold FreshSuppFs.
   eapply Forall_cons; auto.
   
   eapply freshSuppF_coversF; auto.
Qed.


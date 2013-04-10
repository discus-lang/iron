
Require Export Iron.SystemF2Effect.Step.Frame.
Require Export Iron.SystemF2Effect.Step.Preservation.
Require Export Iron.SystemF2Effect.Store.
Require Export Iron.SystemF2Effect.Type.Relation.SubsVisibleT.


(* Multistep evaluation. *)
Inductive Steps
    :  store -> stprops -> stack -> exp
    -> store -> stprops -> stack -> exp -> Prop :=
 | SsNone 
   :  forall ss sp fs x
   ,  Steps  ss  sp  fs  x   ss  sp  fs  x

 | SsCons
   :  forall ss1 sp1 fs1 x1
             ss2 sp2 fs2 x2
             ss3 sp3 fs3 x3 
   ,  STEPF  ss1 sp1 fs1 x1  ss2 sp2 fs2 x2  
   -> Steps  ss2 sp2 fs2 x2  ss3 sp3 fs3 x3 
   -> Steps  ss1 sp1 fs1 x1  ss3 sp3 fs3 x3.

Hint Constructors Steps.


Lemma steps_trans
 :  forall ss1 sp1 fs1 x1 
           ss2 sp2 fs2 x2
           ss3 sp3 fs3 x3
 ,  Steps  ss1 sp1 fs1 x1  ss2 sp2 fs2 x2
 -> Steps  ss2 sp2 fs2 x2  ss3 sp3 fs3 x3
 -> Steps  ss1 sp1 fs1 x1  ss3 sp3 fs3 x3.
Proof.
 intros.
 induction H; eauto.
Qed.


Lemma steps_preservation
 :  forall se  sp  ss  fs  x  
               sp' ss' fs' x'  
           t   e
 ,  WfFS   se  sp  ss  fs 
 -> LiveS  ss  fs  
 -> LiveE  fs  e 
 -> TYPEC  nil nil se  sp  fs  x   t   e
 -> Steps  ss  sp  fs  x   ss' sp' fs' x'
 -> (exists se' e'
    ,  extends se' se
    /\ WfFS    se' sp' ss' fs' 
    /\ LiveS   ss' fs'
    /\ LiveE   fs' e'
    /\ SubsVisibleT nil sp e e'
    /\ TYPEC   nil nil se' sp' fs' x' t e').
Proof.
 intros. gen se e.
 induction H3; intros.
 - exists se. exists e. rip.
   eapply subsVisibleT_refl. 
   inverts H2. eauto.

 - lets D: preservation H2 H; eauto.
   destruct D  as [se2].
   destruct H5 as [e2]. rip.
   spec IHSteps se2. rip.
   spec IHSteps e2.  rip.
   destruct IHSteps as [se3].
   destruct H10     as [e3]. rip.
   exists se3. exists e3. rip.
   + eapply extends_trans; eauto.

   + eapply subsVisibleT_trans; eauto.
     assert (extends sp2 sp1).
      eapply stepf_stprops_extends.
     eauto.

     eapply subsVisibleT_strengthen; eauto.
Qed.

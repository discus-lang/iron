
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Step.Preservation.
Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.Type.Relation.SubsVisibleT.


(********************************************************************)
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
   ,  StepF  ss1 sp1 fs1 x1  ss2 sp2 fs2 x2  
   -> Steps  ss2 sp2 fs2 x2  ss3 sp3 fs3 x3 
   -> Steps  ss1 sp1 fs1 x1  ss3 sp3 fs3 x3.

Hint Constructors Steps.


(********************************************************************)
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


Lemma steps_extends_stprops
 :  forall ss sp fs x  ss' sp' fs' x'
 ,  Steps  ss sp fs x  ss' sp' fs' x'
 -> extends sp' sp.
Proof.
 intros. 
 induction H. eauto.
 eapply stepF_extends_stprops in H.
 eapply extends_trans; eauto.
Qed.


(* Preservation for multi-step evaluation. *)
Lemma steps_preservation
 :  forall se  sp  ss  fs  x  
               sp' ss' fs' x'  
           t   e
 ,  WfFS   se  sp  ss  fs 
 -> LiveS  ss  fs  
 -> LiveE  fs  e 
 -> TypeC  nil nil se  sp  fs  x   t   e
 -> Steps  ss  sp  fs  x   ss' sp' fs' x'
 -> (exists se' e'
    ,  WfFS    se' sp' ss' fs' 
    /\ LiveS   ss' fs'
    /\ LiveE   fs' e'
    /\ SubsVisibleT nil sp' sp e e'
    /\ TypeC    nil nil se' sp' fs' x' t e').
Proof.
 intros. gen se e.
 induction H3; intros.
 - exists se. exists e. 
   intuition.
   eapply subsVisibleT_refl. 
   inverts H2. eauto.

 - lets D: preservation H2 H; eauto.
   destruct D  as [se2].
   destruct H5 as [e2].  rip.
   spec IHSteps se2.     rip.
   spec IHSteps e2.      rip.
   destruct IHSteps as [se3].
   destruct H9      as [e3].
   exists se3. exists e3. 
   intuition.
   + eapply subsVisibleT_trans; eauto.
     * eapply subsVisibleT_stprops_extends.
       eapply steps_extends_stprops; eauto.
       eauto.

     * have (extends sp2 sp1)
        by (eapply stepF_extends_stprops; eauto).
       eapply subsVisibleT_spVis_strengthen; eauto.
Qed.

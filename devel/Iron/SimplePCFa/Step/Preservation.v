
Require Import Iron.SimplePCFa.Step.Frame.
Require Import Iron.SimplePCFa.Step.Prim.
Require Import Iron.SimplePCFa.Step.TfJudge.
Require Import Iron.SimplePCFa.Value.SubstValExp.
Require Import Iron.SimplePCFa.Value.


Lemma preservation
 :  forall te fs fs' x x' t
 ,  TYPEC te fs  x  t
 -> STEPF    fs  x    fs' x'
 -> TYPEC te fs' x' t.
Proof.
 intros te fs fs' x x' t HT HS. gen t.
 induction HS; intros; eauto.

 Case "SfPrim".
  destruct H; inverts HT; inverts_type; eauto.
   SCase "SpAppLam".
    eapply TcExp; eauto.
    eapply subst_val_exp; eauto.

   SCase "SpAppFix".
    inverts H4.
    eapply TcExp; eauto.
    eapply TxApp; eauto.
     eapply subst_val_val; eauto.

 Case "SfPush". 
  inverts HT. inverts_type. eauto.

 Case "SfPop".
  inverts HT. inverts_type.
  inverts H.
  eapply TcExp; eauto.
  eapply subst_val_exp; eauto.
Qed.



Require Export Iron.Language.SystemF2r.Ty.
Require Export Iron.Language.SystemF2r.Ki.
Require Export Iron.Language.SystemF2r.Collection.


(* Kinds judgement assigns a kind to a type *)
Inductive KIND : kienv -> ty -> ki -> Prop :=
 | KIConFun
   :  forall ke
   ,  KIND ke (TCon TyConFun) (KFun KData (KFun KData KData))

 | KIConData
   :  forall ke i k
   ,  KIND ke (TCon (TyConData i k)) k

 | KIVar
   :  forall ke i k 
   ,  has    i k ke
   -> KIND   ke (TVar i) k

 | KIForall
   :  forall ke ke' t
   ,  also   0 KData ke ke'
   -> KIND   ke' t KData
   -> KIND   ke  (TForall t) KData

 | KIApp 
   :  forall ke t1 t2 k11 k12
   ,  KIND   ke t1 (KFun k11 k12)
   -> KIND   ke t2 k11
   -> KIND   ke (TApp t1 t2) k12.
Hint Constructors KIND.


(* Invert all hypothesis that are compound kinding statements. *)
Ltac inverts_kind :=
 repeat 
  (match goal with 
   | [ H: KIND _ (TCon _)    _  |- _ ] => inverts H
   | [ H: KIND _ (TVar _)    _  |- _ ] => inverts H
   | [ H: KIND _ (TForall _) _  |- _ ] => inverts H
   | [ H: KIND _ (TApp _ _) _   |- _ ] => inverts H
   end).


(* A well kinded type is well formed *)
Lemma kind_wfT
 :  forall ke t k
 ,  KIND ke t k
 -> wfT  (length ke) t.
Proof.
 intros ke t k HK. gen ke k.
 induction t; intros; inverts_kind; eauto.
 eapply WfT_TForall. eapply IHt in H2.
 admit.
Qed.
Hint Resolve kind_wfT.


Lemma kind_wfT_Forall
 :  forall ks ts
 ,  Forall (fun t => KIND ks t KData) ts
 -> Forall (wfT (length ks)) ts.
Proof.
 intros. repeat nforall. eauto.
Qed.
Hint Resolve kind_wfT_Forall.


Lemma kind_wfT_Forall2
 :  forall (ke: kienv) ts ks
 ,  Forall2 (KIND ke) ts ks
 -> Forall (wfT (length ke)) ts.
Proof.
 intros.
 eapply (Forall2_Forall_left (KIND ke)).
 nforall. intros. eauto. eauto.
Qed.
Hint Resolve kind_wfT_Forall2.


(* If a type is well kinded in an empty environment,
   then that type is closed. *)
Lemma kind_empty_is_closed
 :  forall t k
 ,  KIND nil t k 
 -> closedT t.
Proof.
 intros. unfold closedT.
 have (@length ki nil = 0).
  rewrite <- H0.
  eapply kind_wfT. eauto.
Qed.
Hint Resolve kind_empty_is_closed.


(* Weakening kind environments. *)
Lemma kind_kienv_insert
 :  forall ke ke' i t k1 k2
 ,  also i k2 ke ke' 
 -> KIND ke t k1
 -> KIND ke' (liftTT 1 i t) k1.
Proof.
 intros. gen i ke ke' k1.
 induction t; intros; simpl; inverts_kind; eauto.

 Case "TVar".
  lift_cases; intros; repeat nnat; auto.
  eapply KIVar.

 admit.
 admit. 
 admit.
Qed.

 


 (******
   ** for larger environment use 
        type : relation tyenv -> relation env
        kind : relation kienv -> relation env

        type (has i t) env env'
        kind (has i k) env env'

       

unfold has.
  unfold keAtK in *.
  unfold keKi  in *.
  subst.
  lift_cases; intros; repeat nnat; auto. 
  eapply KIVar. unfold keAtK. eauto.
  eapply KIVar. unfold keAtK. eauto.
  
 Case "TForall".
  unfold keKi in *.
  unfold keK  in *.
  subst.
  eapply KIForall.
  unfold keK in *. eauto. 
  rewrite insert_rewind.
  eapply IHt. eauto. auto.
Qed.


Lemma kind_kienv_weaken
 :  forall ke t k1 k2
 ,  KIND  ke         t             k1
 -> KIND (ke :> k2) (liftTT 1 0 t) k1.
Proof.
 intros.
 assert (ke :> k2 = insert 0 k2 ke). simpl.
   destruct ke; auto.
 rewrite H0. eapply kind_kienv_insert. 
 unfold keKi. eauto. auto.
Qed.

*****)
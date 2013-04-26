
Require Export Iron.Language.SystemF2Data.Kind.
Require Export Iron.Language.SystemF2Data.Type.Exp.
Require Export Iron.Language.SystemF2Data.Type.Operator.LiftTT.
Require Export Iron.Language.SystemF2Data.Type.Operator.SubstTT.

(********************************************************************)
(* Kinds judgement assigns a kind to a type *)
Inductive KIND : kienv -> ty -> ki -> Prop :=
 | KIConFun
   :  forall ke
   ,  KIND ke (TCon TyConFun) (KFun KStar (KFun KStar KStar))

 | KIConData
   :  forall ke i k
   ,  KIND ke (TCon (TyConData i k)) k

 | KIVar
   :  forall ke i k
   ,  get i ke = Some k
   -> KIND ke (TVar i) k

 | KIForall
   :  forall ke t
   ,  KIND (ke :> KStar) t           KStar
   -> KIND ke            (TForall t) KStar

 | KIApp 
   :  forall ke t1 t2 k11 k12
   ,  KIND ke t1 (KFun k11 k12)
   -> KIND ke t2 k11
   -> KIND ke (TApp t1 t2) k12.
Hint Constructors KIND.


(********************************************************************)
(* Invert all hypothesis that are compound kinding statements. *)
Ltac inverts_kind :=
 repeat 
  (match goal with 
   | [ H: KIND _ (TCon _)    _  |- _ ] => inverts H
   | [ H: KIND _ (TVar _)    _  |- _ ] => inverts H
   | [ H: KIND _ (TForall _) _  |- _ ] => inverts H
   | [ H: KIND _ (TApp _ _) _   |- _ ] => inverts H
   end).


(********************************************************************)
(* A well kinded type is well formed *)
Lemma kind_wfT
 :  forall ke t k
 ,  KIND ke t k
 -> wfT  (length ke) t.
Proof.
 intros ke t k HK. gen ke k.
 induction t; intros; inverts_kind; burn.
 - eapply WfT_TForall.
   rrwrite (S (length ke) = length (ke :> KStar)).
   eauto.
Qed.
Hint Resolve kind_wfT.


Lemma kind_wfT_Forall
 :  forall ks ts
 ,  Forall (fun t => KIND ks t KStar) ts
 -> Forall (wfT (length ks)) ts.
Proof. snorm; eauto. Qed.
Hint Resolve kind_wfT_Forall.


Lemma kind_wfT_Forall2
 :  forall (ke: kienv) ts ks
 ,  Forall2 (KIND ke) ts ks
 -> Forall (wfT (length ke)) ts.
Proof.
 intros.
 eapply (Forall2_Forall_left (KIND ke)); snorm; eauto.
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


(********************************************************************)
(* Weakening kind environments. *)
Lemma kind_kienv_insert
 :  forall ke ix t k1 k2
 ,  KIND ke t k1
 -> KIND (insert ix k2 ke) (liftTT 1 ix t) k1.
Proof.
 intros. gen ix ke k1.
 induction t; intros; simpl; inverts_kind; eauto.

 - Case "TVar".
   lift_cases; intros; repeat nnat; auto.

 - Case "TForall".
   apply KIForall.
   rewrite insert_rewind. auto.
Qed.


Lemma kind_kienv_weaken
 :  forall ke t k1 k2
 ,  KIND  ke         t             k1
 -> KIND (ke :> k2) (liftTT 1 0 t) k1.
Proof.
 intros.
 assert (ke :> k2 = insert 0 k2 ke). simpl.
   destruct ke; auto.
 rewrite H0. apply kind_kienv_insert. auto.
Qed.


(********************************************************************)
(* Substitution of types in types preserves kinding.
   Must also subst new new type into types in env higher than ix
   otherwise indices that reference subst type are broken, and 
   the resulting type env would not be well formed *)
Theorem subst_type_type_ix
 :  forall ix ke t1 k1 t2 k2
 ,  get ix ke = Some k2
 -> KIND ke t1 k1
 -> KIND (delete ix ke) t2 k2
 -> KIND (delete ix ke) (substTT ix t2 t1) k1.
Proof.
 intros. gen ix ke t2 k1 k2.
 induction t1; intros; simpl; inverts_kind; eauto.

 - Case "TVar".
   fbreak_nat_compare.
   SCase "n = ix".
    rewrite H in H4.
    inverts H4. auto.

   SCase "n < ix".
    apply KIVar. rewrite <- H4.
    apply get_delete_above; auto.

   SCase "n > ix".
    apply KIVar. rewrite <- H4.
    destruct n.
     burn.
     simpl. nnat. apply get_delete_below. omega.

 - Case "TForall".
   apply KIForall.
   rewrite delete_rewind.
   eapply IHt1; eauto.
    apply kind_kienv_weaken; auto.
Qed.


Theorem subst_type_type_ix_forall2
 :  forall ix ke t2 k2 ts ks
 ,  get ix ke = Some k2
 -> Forall2 (KIND ke) ts ks
 ->          KIND (delete ix ke) t2 k2
 -> Forall2 (KIND (delete ix ke)) (map (substTT ix t2) ts) ks.
Proof.
 intros.
 eapply Forall2_map_left.
 apply (Forall2_impl
            (fun t k => KIND ke t k)
            (fun t k => KIND (delete ix ke) (substTT ix t2 t) k)
            ts ks).
  intros. eapply subst_type_type_ix; eauto.
  eauto.
Qed.  


Theorem subst_type_type
 :  forall ke t1 k1 t2 k2
 ,  KIND (ke :> k2) t1 k1
 -> KIND ke         t2 k2
 -> KIND ke (substTT 0 t2 t1) k1.
Proof.
 intros.
 unfold substTT.
 rrwrite (ke = delete 0 (ke :> k2)).
 eapply subst_type_type_ix; burn.
Qed.


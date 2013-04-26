
Require Export Iron.Language.SystemF2Data.Type.Exp.
Require Export Iron.Language.SystemF2Data.Type.Relation.WfT.

(********************************************************************)
(* Type Utils *)
(* Get the type constructor of a type, if any *)
Fixpoint getCtorOfType (tt: ty) : option tycon :=
 match tt with
 | TCon tc   => Some tc
 | TApp t1 _ => getCtorOfType t1
 | _         => None
 end.


(* Construct a type application from a constructor type
   and a list of argument types. *)
Fixpoint makeTApps (t1: ty) (tt: list ty) : ty :=
 match tt with
 | nil     => t1
 | t :: ts => makeTApps (TApp t1 t) ts
 end.


(* Take the left most type along the in a tree of type applications. *)
Fixpoint takeTCon (tt: ty) : ty :=
 match tt with 
 | TApp t1 t2 => takeTCon t1
 | _          => tt
 end.


(* Take the list of arguments in a nested type application, 
   walking down the spine. *)
Fixpoint takeTArgs (tt: ty) : list ty :=
 match tt with 
 | TApp t1 t2 => snoc t2 (takeTArgs t1)
 | _          => cons tt nil
 end.


(* Break apart a type application into the constructor type
   and a list of argument types. *)
Definition takeTApps (tt: ty) : (ty * list ty) 
 := (takeTCon tt, takeTArgs tt).


(********************************************************************)
Lemma makeTApps_snoc
 : forall t1 t2 t3 ts
 , makeTApps (TApp t1 t2) (snoc t3 ts) 
 = TApp (makeTApps t1 (cons t2 ts)) t3.
Proof.
 intros. gen t1 t2.
 induction ts; simpl; burn.
Qed.


Lemma makeTApps_snoc'
 :  forall t1 t2 ts
 ,  makeTApps t1 (snoc t2 ts)
 =  TApp (makeTApps t1 ts) t2.
Proof.
 intros. gen t1 t2.
 induction ts; intros.
  auto.
  simpl. auto.
Qed.


Lemma takeTCon_makeTApps
 :  forall t1 ts
 ,  takeTCon (makeTApps t1 ts) = takeTCon t1.
Proof.
 intros. gen t1.
 induction ts; intros; simpl; auto.
  rewrite IHts. burn.
Qed.    
Hint Resolve takeTCon_makeTApps.


Lemma makeTApps_takeTCon
 :  forall t1 t2 ts  
 ,  makeTApps t1 ts = t2
 -> takeTCon t1     = takeTCon t2.
Proof.
 intros. gen t1 t2.
 induction ts; intros.
 + simpl in H. subst. auto.
 + eapply IHts in H. simpl in H. auto.
Qed.
Hint Resolve makeTApps_takeTCon.


Lemma getCtorOfType_makeTApps
 :  forall tc t1 ts
 ,  getCtorOfType t1 = Some tc
 -> getCtorOfType (makeTApps t1 ts) = Some tc.
Proof.
 intros. gen t1.
 induction ts; intros.
 + auto.
 + snorm.
Qed.
Hint Resolve getCtorOfType_makeTApps.


Lemma makeTApps_rewind
 :  forall t1 t2 ts
 ,  makeTApps (TApp t1 t2) ts = makeTApps t1 (t2 :: ts).
Proof. intros. auto. Qed.


Lemma makeTApps_tycon_eq
 :  forall tc1 tc2 ts1 ts2
 ,  makeTApps (TCon tc1) ts1 = makeTApps (TCon tc2) ts2
 -> tc1 = tc2.
Proof.
 intros.
 have HT: ( takeTCon (makeTApps (TCon tc1) ts1) 
          = takeTCon (makeTApps (TCon tc2) ts2)) 
  by (rewritess; snorm).
 repeat (rewrite takeTCon_makeTApps in HT).
 simpl in HT. inverts HT. auto.
Qed.


Lemma makeTApps_args_eq
 :  forall tc ts1 ts2
 ,  makeTApps (TCon tc) ts1  = makeTApps (TCon tc) ts2
 -> ts1 = ts2.
Proof.
 intros. gen ts2.
 induction ts1 using rev_ind; intros.
 - Case "ts1 = nil".
   simpl in H. 
   destruct ts2.
   + SCase "ts2 ~ nil".
     auto.

   + SCase "ts2 ~ cons".
     simpl in H.
     lets D: @snocable ty ts2. inverts D.
     * simpl in H. nope.
     * destruct H0 as [t2].
       destruct H0 as [ts2']. 
       subst.
       rewrite makeTApps_snoc in H. nope.
   
 - Case "ts1 ~ snoc".
   lets D: @snocable ty ts2. inverts D.
   + SCase "ts2 ~ nil".
     simpl in H.
     rewrite app_snoc in H.
     rewrite app_nil_right in H.
     rewrite makeTApps_snoc' in H.
     nope.

   + SCase "ts2 ~ snoc" .
     dest t. dest ts'. subst.
     rewrite app_snoc in H.
     rewrite app_snoc. 
     snorm.
     rewrite makeTApps_snoc' in H.
     rewrite makeTApps_snoc' in H.
     inverts H.
     eapply IHts1 in H1. subst. 
     auto.
Qed.


Lemma makeTApps_eq_params
 : forall tc1 tc2 ts1 ts2
 ,  makeTApps (TCon tc1) ts1 = makeTApps (TCon tc2) ts2
 -> tc1 = tc2 /\ ts1 = ts2.
Proof.
 intros.
 rrwrite (tc1 = tc2)
  by (eapply makeTApps_tycon_eq; eauto).
 rrwrite (ts1 = ts2)
  by (eapply makeTApps_args_eq; eauto).
 auto.
Qed.


Lemma makeTApps_wfT
 :  forall n t1 ts
 ,  wfT n t1 
 -> Forall (wfT n) ts
 -> wfT n (makeTApps t1 ts).
Proof.
 intros. gen t1.
 induction ts; intros.
 - simpl. auto.
 - simpl.
   inverts H0.
   have HS: (ts = nil \/ (exists t ts', ts = t <: ts'))
    by (apply snocable).
   inverts HS.
   + simpl. auto. 
   + dest H0. dest H0. subst.
     eapply IHts; auto.
Qed.


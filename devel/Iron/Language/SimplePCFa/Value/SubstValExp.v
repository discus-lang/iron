
Require Export Iron.Language.SimplePCFa.Value.Exp.
Require Export Iron.Language.SimplePCFa.Value.Subst.
Require Export Iron.Language.SimplePCFa.Value.TyJudge.


(* Weakening the type environment in typine judgements.
   We can insert a new type into the type environment, provided we
   lift existing references to types higher in the stack across
   the new one. *)
Lemma typex_tyenv_insert
 :  forall te ix x t1 t2
 ,  TYPEX te x t1
 -> TYPEX (insert ix t2 te) (liftXX ix x) t1.
Proof.
 intros te ix x t1 t2 HT. gen ix te t1 t2.
 induction x using exp_mutind with 
  (PV := fun v1 => forall ix te t1 t2
      ,  TYPEV te v1 t1
      -> TYPEV (insert ix t2 te) (liftXV ix v1) t1);
 rip; inverts_type;
  try (solve [simpl; snorm]).

 Case "XLam".
  simpl.
  apply TvLam.
  rewrite insert_rewind. 
  eapply IHx. burn.

 Case "XFix".
  simpl.
  destruct t;  nope.
  destruct t1; nope.
  inverts H.
  apply TvFix.
  rewrite insert_rewind.
  apply IHx; burn.

 Case "XLet".
  simpl.
  apply TxLet; eauto.
  rewrite insert_rewind; auto.

 Case "XApp".
  simpl.
  eapply TxApp; eauto.
Qed.


Lemma typex_tyenv_weaken
 :  forall te x t1 t2
 ,  TYPEX  te        x            t1
 -> TYPEX (te :> t2) (liftXX 0 x) t1.
Proof.
 intros.
 rrwrite (te :> t2 = insert 0 t2 te).
 burn using typex_tyenv_insert.
Qed.


Lemma typev_tyenv_weaken
 :  forall te v t1 t2
 ,  TYPEV  te        v            t1
 -> TYPEV (te :> t2) (liftXV 0 v) t1.
Proof.
 intros.
 rrwrite (te :> t2 = insert 0 t2 te).
 assert (TYPEX (insert 0 t2 te) (liftXX 0 (XVal v)) t1).
  eapply typex_tyenv_insert. eauto.
 inverts H0. auto.
Qed.


Theorem subst_val_exp_ix
 :  forall ix te x1 v2 t1 t2
 ,  get  ix te = Some t2
 -> TYPEX te             x1 t1
 -> TYPEV (delete ix te) v2 t2
 -> TYPEX (delete ix te) (substVX ix v2 x1) t1.
Proof.
 intros. gen ix te v2 t1 t2.
 induction x1 using exp_mutind with
  (PV := fun v1 => forall ix te v2 t1 t2
      ,  get ix te = Some t2
      -> TYPEV te             v1 t1
      -> TYPEV (delete ix te) v2 t2
      -> TYPEV (delete ix te) (substVV ix v2 v1) t1);
  intros; simpl; inverts_type; 
   try (solve [snorm; eauto]).

 Case "VVar".
  snorm. subst.
  rewrite H in H4. inverts H4. auto.

  eapply TvVar.
   destruct n. 
    omega.
    simpl. snorm. down. eapply get_delete_below. omega.

 Case "VLam".
  apply TvLam.
  rewrite delete_rewind.
  eapply IHx1; eauto.
   simpl.
   apply typev_tyenv_weaken. auto.
     
 Case "VFix".
  destruct t1. nope.
  destruct t.  nope.
  inverts H0.
  eapply TvFix.
   rewrite delete_rewind.
   eapply IHx1; eauto.
    simpl.
    apply typev_tyenv_weaken. auto.
    
 Case "XLet".
  eapply TxLet. eauto.
   rewrite delete_rewind.
   eapply IHx1_2; eauto.
    simpl.
    apply typev_tyenv_weaken. auto.
Qed.


Theorem subst_val_exp
 :  forall te x1 t1 v2 t2
 ,  TYPEX  (te :> t2) x1                t1
 -> TYPEV  te         v2                t2
 -> TYPEX  te         (substVX 0 v2 x1) t1.
Proof.
 intros.
 rrwrite (te = delete 0 (te :> t2)). 
 eapply subst_val_exp_ix; burn.
Qed.


Theorem subst_val_val
 :  forall te v1 t1 v2 t2
 ,  TYPEV  (te :> t2) v1                t1
 -> TYPEV  te         v2                t2
 -> TYPEV  te         (substVV 0 v2 v1) t1.
Proof.
 intros.
 rrwrite (te = delete 0 (te :> t2)). 
 assert (TYPEX (delete 0 (te :> t2)) (substVX 0 v2 (XVal v1)) t1).
  eapply subst_val_exp; eauto.
 snorm. inverts H1. auto.
Qed.



Require Import Iron.Language.SystemF2Effect.Value.Relation.TyJudge.


(* Weakening Type Env in Type Judgement.
   We can insert a new type into the type environment, provided we
   lift existing references to types higher in the stack across
   the new one. *)
Lemma type_tyenv_insert
 :  forall ke te se sp ix x t1 e1 t2
 ,  TypeX  ke te se sp x t1 e1
 -> TypeX  ke (insert ix t2 te) se sp (liftXX 1 ix x) t1 e1.
Proof.
 intros. gen ix ke se sp te t1 e1 t2.
 induction x using exp_mutind with 
  (PV := fun v => forall ix ke se sp te t1 t2
      ,  TypeV ke te se sp v t1 
      -> TypeV ke (insert ix t2 te) se sp (liftXV 1 ix v) t1)
  ; intros; inverts_type; simpl; eauto.

 - Case "VVar".
   nnat; lift_cases; burn.

 - Case "VLam".
   apply TvLam; eauto.
   rewrite insert_rewind. auto.

 - Case "VLAM".
   apply TvLAM.
   have ( liftTE 0 (insert ix t2 te)
        = insert ix (liftTT 1 0 t2) (liftTE 0 te))
    by (unfold liftTE; rewrite map_insert; auto).
   rewritess. eauto.

 - Case "XLet".
   apply TxLet; eauto. 
   rewrite insert_rewind. eauto.

 - Case "XPrivate".
   eapply TxPrivate with (t := t) (e := e); eauto.
   have ( liftTE 0 (insert ix t2 te)
        = insert ix (liftTT 1 0 t2) (liftTE 0 te))
    by (unfold liftTE; rewrite map_insert; auto).
   rewritess. eauto.

 - Case "XExtend".
   eapply TxExtend; eauto.
   have ( liftTE 0 (insert ix t2 te)
        = insert ix (liftTT 1 0 t2) (liftTE 0 te))
    by (unfold liftTE; rewrite map_insert; auto).
   rewritess. eauto.
Qed. 


(* We can push a new type onto the environment stack provided
   we lift references to existing types across the new one. *)
Lemma type_tyenv_weaken1
 :  forall ke te se sp x t1 e1 t2
 ,  TypeX  ke te se sp x t1 e1
 -> TypeX  ke (te :> t2) se sp (liftXX 1 0 x) t1 e1.
Proof.
 intros.
 rrwrite (te :> t2 = insert 0 t2 te).
 burn using type_tyenv_insert.
Qed.


(* We can push a new type into the enviroment of a type-of-value 
   judgement provided we lift references to existing types across
   the new one *)
Lemma typev_tyenv_weaken1
 :  forall ke te se sp v t1 t2
 ,  TypeV  ke te se sp v t1
 -> TypeV  ke (te :> t2) se sp (liftXV 1 0 v) t1.
Proof.
 intros.
 have HX: (TypeX ke te se sp (XVal v) t1 (TBot KEffect)).
 eapply type_tyenv_weaken1 in HX.
 simpl in HX. inverts HX. eauto.
Qed.


(* We can several new types onto the environment stack provided
   we lift referenes to existing types across the new one. *)
Lemma type_tyenv_weaken_append
 :  forall ke te se sp te' x t1 e1
 ,  TypeX  ke te se sp x t1 e1
 -> TypeX  ke (te >< te') se sp (liftXX (length te') 0 x) t1 e1.
Proof.
 intros.
 induction te'; simpl.
  - burn.

  - rrwrite (S (length te') = length te' + 1).
    rrwrite (length te' + 1 = 1 + length te').
    rewrite <- liftXX_plus.
    eapply type_tyenv_weaken1.
    burn.
Qed.


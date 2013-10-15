
Require Import Iron.Language.SystemF2Effect.Value.Relation.TyJudge.


(* Uniqueness of typing.
   Checking an expression always returns a unique type an effect. *)
Lemma typex_unique
 :  forall ke te se sp x t1 e1 t2 e2
 ,  TypeX  ke te se sp x t1 e1
 -> TypeX  ke te se sp x t2 e2
 -> t1 = t2 /\ e1 = e2.
Proof.
 intros. gen ke te se sp t1 e1 t2 e2.
 induction x using exp_mutind with 
  (PV := fun v1 => forall ke te se sp t1 t1'
      ,  TypeV ke te se sp v1 t1
      -> TypeV ke te se sp v1 t1'
      -> t1 = t1');
  intros; 
   try (solve [inverts_type; try congruence]);
   inverts_type; auto.

 - Case "VLam".
   spec IHx H9 H10. 
   burn.

 - Case "VLAM".
   spec IHx H8 H7.
   burn.

 - Case "XVal".
   spec IHx H6 H5.
   burn.

 - Case "XLet".
   spec IHx1 H11 H13.
   spec IHx2 H12 H14. 
   rip.

 - Case "XApp".
   spec IHx  H7  H6.
   spec IHx0 H10 H11.
   subst. inverts IHx. auto.

 - Case "VAPP". 
   spec IHx H7 H6.
   inverts IHx. auto.

 - Case "XOp1".
   spec IHx H10 H11.
   subst. 
   rip; congruence.

 - Case "XPrivate".
   spec IHx H8 H10.
   rip; congruence.

 - Case "XExtend".
   spec IHx H11 H13.
   rip; congruence.

 - Case "XAlloc".
   spec IHx H10 H11.
   subst. burn.

 - Case "XRead".
   spec IHx H10 H11.
   inverts IHx. auto.
Qed.

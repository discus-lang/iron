
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.


(* Uniqueness of typing *)
Lemma type_unique
 :  forall ke te se x t1 e1 t2 e2
 ,  TYPEX ke te se x t1 e1
 -> TYPEX ke te se x t2 e2
 -> t1 = t2 /\ e1 = e2.
Proof.
 intros. gen ke te se t1 e1 t2 e2.
 induction x using exp_mutind with 
  (PV := fun v1 => forall ke te se t1 t1'
      ,  TYPEV ke te se v1 t1
      -> TYPEV ke te se v1 t1'
      -> t1 = t1');
  intros; 
   try (solve [inverts_type; try congruence]);
   inverts_type; auto.

 Case "VLam".
  spec IHx H8 H9. burn.

 Case "VLAM".
  spec IHx H7 H6. burn.

 Case "XVal".
  spec IHx H5 H4. burn.

 Case "XLet".
  spec IHx1 H10 H12.
  spec IHx2 H11 H13. 
  rip.

 Case "XApp".
  spec IHx  H6 H5.
  spec IHx0 H9 H10.
  subst.
  inverts IHx. auto.

 Case "VAPP". 
  spec IHx H6 H5.
  inverts IHx.
  auto.

 Case "XNew".
  spec IHx H7 H9.
  rip.

 Case "XUse".
  spec IHx H8 H7.
  rip.

 Case "XAlloc".
  spec IHx H9 H10.
  subst. burn.

 Case "XRead".
  spec IHx H9 H10.
  inverts IHx. auto.
Qed.

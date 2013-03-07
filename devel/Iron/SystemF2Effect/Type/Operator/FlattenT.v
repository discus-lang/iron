
Require Export Iron.SystemF2Effect.Type.Exp.Base.
Require Export Iron.SystemF2Effect.Type.Relation.KindT.
Require Export Iron.SystemF2Effect.Type.Relation.KindTs.


Fixpoint flattenT (tt : ty) : list ty
 := match tt with
    | TVar    _     => tt :: nil
    | TForall _ _   => tt :: nil
    | TApp    _ _   => tt :: nil
    | TSum t1 t2    => flattenT t1 ++ flattenT t2
    | TBot    _     => nil
    | TCon0   _     => tt :: nil
    | TCon1   _ _   => tt :: nil
    | TCon2   _ _ _ => tt :: nil
    | TCap    _     => tt :: nil
    end.


Lemma flattenT_kindTs
 :  forall ke sp t1 k
 ,  KindT  ke sp t1 k
 -> KindTs ke sp (flattenT t1) k.
Proof.
 intros. gen ke sp.
 induction t1; intros; simpl; eauto.

 Case "TSum". 
  inverts H.
  unfold KindTs in *.
   eapply Forall_app; eauto.
Qed.
Hint Resolve flattenT_kindTs.



Require Export Iron.Language.SimplePCFa.Value.Lower.
Require Export Iron.Language.SimplePCFa.Value.Refs.
Require Export Iron.Language.SimplePCFa.Value.Exp.
Require Export Iron.Language.SimplePCFa.Type.


Inductive TYPEV : tyenv -> val -> ty -> Prop := 
 | TvVar
   :  forall te i t
   ,  get i te = Some t
   -> TYPEV te (VVar i) t

 | TvConstBool
   :  forall te b
   ,  TYPEV te (VConst (CBool b)) tBool

 | TvConstNat
   :  forall te n
   ,  TYPEV te (VConst (CNat n))  tNat

 | TvLam
   :  forall te t1 t2 x2
   ,  TYPEX (te :> t1) x2 t2
   -> TYPEV te (VLam t1 x2) (TFun t1 t2)

 (* Require all fixpoints to be functions so that values of type Nat must be 
    constants. If we didn't do this then with (Succ (fix ...)) the inner
    fixpoint could be assigned the Nat type, so Succ would need to force
    evaluation of its body. *)
 | TvFix
   :  forall te t1 t2 v2
   ,  TYPEV (te :> (TFun t1 t2))  v2  (TFun t1 t2)
   -> TYPEV te (VFix (TFun t1 t2) v2) (TFun t1 t2)

 with TYPEX : tyenv -> exp -> ty -> Prop :=
 | TxVal
   :  forall te v t1
   ,  TYPEV te v t1
   -> TYPEX te (XVal v) t1

 | TxLet
   :  forall te t1 x1 t2 x2
   ,  TYPEX te          x1 t1 
   -> TYPEX (te :> t1)  x2 t2
   -> TYPEX te (XLet t1 x1 x2) t2

 | TxApp
   :  forall te t11 t12 v1 v2
   ,  TYPEV te v1 (TFun t11 t12) 
   -> TYPEV te v2 t11
   -> TYPEX te (XApp v1 v2) t12

 | TxOpSucc
   :  forall te v1
   ,  TYPEV te v1 tNat
   -> TYPEX te (XOp1 OSucc v1) tNat

 | TxOpPred
   :  forall te v1
   ,  TYPEV te v1 tNat
   -> TYPEX te (XOp1 OPred v1) tNat

 | TxOpIsZero
   :  forall te v1
   ,  TYPEV te v1 tNat
   -> TYPEX te (XOp1 OIsZero v1) tBool

 | TxIf
   :  forall te v1 x2 x3 tR
   ,  TYPEV te v1 tBool
   -> TYPEX te x2 tR
   -> TYPEX te x3 tR
   -> TYPEX te (XIf v1 x2 x3) tR.
Hint Constructors TYPEV.
Hint Constructors TYPEX.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_type :=
 repeat 
  (match goal with 
   | [ H: TYPEV _ (VVar  _)     _    |- _ ] => inverts H
   | [ H: TYPEV _ (VConst _)    _    |- _ ] => inverts H
   | [ H: TYPEV _ (VLam _ _)    _    |- _ ] => inverts H
   | [ H: TYPEV _ (VFix _)      _    |- _ ] => inverts H
   | [ H: TYPEX _ (XVal _)      _    |- _ ] => inverts H
   | [ H: TYPEX _ (XLet _ _ _)  _    |- _ ] => inverts H
   | [ H: TYPEX _ (XApp _ _)    _    |- _ ] => inverts H
   | [ H: TYPEX _ (XOp1 _ _)    _    |- _ ] => inverts H
   | [ H: TYPEX _ (XIf  _ _ _)  _    |- _ ] => inverts H
   end).


Lemma type_tyenv_delete
 :  forall te x t ix
 ,  ~(refsXX ix x)
 -> TYPEX te x t 
 -> TYPEX (delete ix te) (lowerXX ix x) t.
Proof.
 intros. gen te t ix.
 induction x using exp_mutind with 
  (PV := fun v => forall te t ix
      ,  ~(refsXV ix v)
      -> TYPEV te v t
      -> TYPEV (delete ix te) (lowerXV ix v) t);
 intros; inverts H0; simpl; eauto.

 Case "VVar".
  destruct n.
   eapply TvVar. admit. (* ok list lemma *)
   lift_cases. 
    eapply TvVar. admit. (* ok list lemma *)
    eapply TvVar. eauto.

 Case "VLam".
  eapply TvLam. simpl in H.
  rewrite delete_rewind. eauto.

 Case "VFix".
  eapply TvFix. simpl in H.
  rewrite delete_rewind. eauto.

 Case "XLet".
  eapply TxLet. 
   simpl in H. eauto.
   simpl in H. 
    rewrite delete_rewind. 
    eapply IHx2; eauto.

 Case "XApp".
  simpl in H.
  eapply TxApp; burn.

 Case "XIf".
  simpl in H.
  eapply TxIf; snorm.
   eapply IHx2. eauto. firstorder.
   eapply IHx3. eauto. firstorder.
Qed.
Hint Resolve type_tyenv_delete.


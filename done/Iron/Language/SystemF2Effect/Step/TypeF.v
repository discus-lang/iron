
Require Export Iron.Language.SystemF2Effect.Value.TyJudge.
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.Store.LiveE.


(********************************************************************)
(* Type of a frame stack.
   The frame stack is like a continuation that takes an expression of
   a certain type and produces a new expression. *)
Inductive
 TYPEF :  kienv -> tyenv 
       -> stenv -> stprops 
       -> stack -> ty -> ty 
       -> ty -> Prop := 
 | TfNil 
   :  forall ke te se sp t
   ,  KindT  ke sp t KData
   -> TYPEF  ke te se sp nil t t (TBot KEffect)

 | TfConsLet
   :  forall ke te se sp fs t1 x2 t2 e2 t3 e3
   ,  KindT  ke sp t1 KData
   -> TYPEX  ke (te :> t1) se sp                    x2 t2 e2
   -> TYPEF  ke te         se sp fs                 t2 t3 e3
   -> TYPEF  ke te         se sp (fs :> FLet t1 x2) t1 t3 (TSum e2 e3)

 | TfConsPriv
   :  forall ke te se sp fs t1 t2 e2 n
   ,  not (In (FPriv n) fs)
   -> LiveE  fs e2
   -> TYPEF  ke te se  sp fs              t1 t2 e2
   -> TYPEF  ke te se  sp (fs :> FPriv n) t1 t2 e2.

Hint Constructors TYPEF.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_typef :=
 repeat (try 
  (match goal with 
   | [ H: TYPEF _ _ _ _ (_ :> FLet  _ _) _ _ _ |- _ ] => inverts H
   | [ H: TYPEF _ _ _ _ (_ :> FPriv _)   _ _ _ |- _ ] => inverts H
   end); 
 try inverts_type).


(********************************************************************)
Lemma typef_kind_effect
 :  forall ke te se sp fs t1 t2 e
 ,  TYPEF  ke te se sp fs t1 t2 e
 -> KindT  ke sp e KEffect.
Proof.
 intros.
 induction H; eauto.
Qed.
Hint Resolve typef_kind_effect.


Lemma typef_kind_wfT
 :  forall ke te se sp fs t1 t2 e
 ,  TYPEF  ke te se sp fs t1 t2 e
 -> WfT (length ke) e.
Proof. eauto. Qed.
Hint Resolve typef_kind_wfT.


Lemma typef_kind_t1
 :  forall ke te se sp fs t1 t2 e
 ,  TYPEF  ke te se sp fs t1 t2 e
 -> KindT  ke sp t1 KData.
Proof. 
 intros.
 induction H; auto.
Qed.
Hint Resolve typef_kind_t1.


Lemma typef_kind_t2
 :  forall ke te se sp fs t1 t2 e
 ,  TYPEF  ke te se sp fs t1 t2 e
 -> KindT  ke sp t2 KData.
Proof. 
 intros.
 induction H; auto.
Qed.
Hint Resolve typef_kind_t2.


Lemma typef_stenv_snoc
 :  forall ke te se sp fs t1 t2 t3 e
 ,  ClosedT t3
 -> TYPEF ke te se         sp fs t1 t2 e
 -> TYPEF ke te (t3 <: se) sp fs t1 t2 e.
Proof.
 intros. induction H0; eauto.
Qed.
Hint Resolve typef_stenv_snoc.


Lemma typef_stprops_snoc
 :  forall ke te se sp fs t1 t2 p e
 ,  TYPEF  ke te se sp        fs t1 t2 e
 -> TYPEF  ke te se (p <: sp) fs t1 t2 e.
Proof.
 intros. 
 induction H; eauto.
Qed.
Hint Resolve typef_stprops_snoc.



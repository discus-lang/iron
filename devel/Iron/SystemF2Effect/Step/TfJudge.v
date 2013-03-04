
Require Export Iron.SystemF2Effect.Value.TyJudge.
Require Export Iron.SystemF2Effect.Step.Frame.
Require Export Iron.SystemF2Effect.Store.


(******************************************************************************)
(* Type of a frame stack.
   The frame stack is like a continuation that takes an expression of a certain
   type and produces a new expression. *)
Inductive
 TYPEF :  kienv -> tyenv 
       -> stenv -> stprops 
       -> stack -> ty -> ty 
       -> ty -> Prop := 
 | TfNil 
   :  forall ke te se sp t
   ,  TYPEF  ke te se sp nil t t (TBot KEffect)

 | TfConsLet
   :  forall ke te se sp fs t1 x2 t2 e2 t3 e3
   ,  STOREP sp fs
   -> TYPEX  ke (te :> t1) se sp                    x2 t2 e2
   -> TYPEF  ke te         se sp fs                 t2 t3 e3
   -> TYPEF  ke te         se sp (fs :> FLet t1 x2) t1 t3 (TSum e2 e3)

 | TfConsUse
   :  forall ke te se sp fs t1 t2 e2 n
   ,  not (In (FUse n) fs)
   -> TYPEF  ke te se  sp fs             t1 t2 e2
   -> TYPEF  ke te se  sp (fs :> FUse n) t1 t2 e2.

Hint Constructors TYPEF.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_typef :=
 repeat 
  (try (match goal with 
        | [ H: TYPEF _ _ _ _ (_ :> FLet _ _) _ _ _ |- _ ] => inverts H
        | [ H: TYPEF _ _ _ _ (_ :> FUse _)   _ _ _ |- _ ] => inverts H
        end);
   try inverts_type).


Lemma typef_kind_effect
 :  forall ke te se sp fs t1 t2 e
 ,  TYPEF  ke te se sp fs t1 t2 e
 -> KIND   ke sp e KEffect.
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


(*****************************************************************************)
(* Type of an expression in a frame context. *)
Inductive TYPEC 
   :  kienv -> tyenv 
   -> stenv -> stprops 
   -> stack -> exp 
   -> ty    -> ty -> Prop :=
 | TcExp
   :  forall ke te se sp fs x1 t1 e1 t2 e2 e3
   ,  EquivT ke sp (TSum e1 e2) e3 KEffect
   -> TYPEX  ke te se sp x1 t1 e1
   -> TYPEF  ke te se sp fs t1 t2 e2
   -> TYPEC  ke te se sp fs x1 t2 e3.

Hint Constructors TYPEC.


Ltac inverts_typec :=
 repeat
  (try (match goal with
        | [H: TYPEC _ _ _ _ _ _ _ _ |- _ ] => inverts H
        end);
   try inverts_typef).


Lemma typec_kind_effect
 :  forall ke te se sp fs x t e
 ,  TYPEC  ke te se sp fs x t e
 -> KIND   ke sp e KEffect.
Proof.
 intros.
 induction H; eauto.
Qed.


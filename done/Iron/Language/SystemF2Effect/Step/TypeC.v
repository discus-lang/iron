
Require Export Iron.Language.SystemF2Effect.Value.TyJudge.
Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Step.TypeF.


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
 -> KindT  ke sp e KEffect.
Proof.
 intros.
 induction H; eauto.
Qed.


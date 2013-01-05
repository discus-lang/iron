
Require Import Iron.Language.SystemF2Effect.Kind.
Require Import Iron.Language.SystemF2Effect.Type.KiJudge.
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Wf.
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.TypeKind.
Require Import Iron.Language.SystemF2Effect.Value.TyJudge.WeakStEnv.
Require Import Iron.Language.SystemF2Effect.Value.Exp.
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(* A store is a list of store bindings. *)
Definition store := list stbind.


(* Store typing models the store.
   All types in the store typing have a corresponding binding in
   the store *)
Definition STOREM (se: stenv) (ss: store)
 := length se = length ss.
Hint Unfold STOREM.


(* Well typed store. *)
Definition STORET (se: stenv) (sp: stprops) (ss: store)
 := Forall2 (TYPEB nil nil se sp) ss se.
Hint Unfold STORET.


(* Well formed store. *)
Definition WfS (se: stenv) (sp: stprops) (ss: store)
 := Forall closedT se
 /\ STOREM se    ss
 /\ STORET se sp ss.
Hint Unfold WfS.


Lemma closedT_tRef
 :  forall r1 t2
 ,  closedT t2
 -> closedT (tRef (TCon (TyConRegion r1)) t2).
Proof. 
 intros.
 unfold tRef. auto.
Qed.
Hint Resolve closedT_tRef.


(* Extended store environment models the extended store *)
Lemma storem_snoc
 :  forall se ss t stv
 ,  STOREM se ss
 -> STOREM (t <: se) (stv <: ss).
Proof.
 intros.
 unfold STOREM.
 have (length se = length ss). 
 burn.
Qed.
Hint Resolve storem_snoc.


(* Extended store is well typed under extended store environment *)
Lemma storet_snoc
 :  forall se sp ss r1 v1 t2
 ,  TYPEV  nil nil se sp v1 t2
 -> STORET                                     se  sp                   ss
 -> STORET (tRef (TCon (TyConRegion r1)) t2 <: se) sp (StValue r1 v1 <: ss).
Proof.
 intros.
 set (tRef' := tRef (TCon (TyConRegion r1)) t2).

 assert (TYPEB nil nil (tRef' <: se) sp (StValue r1 v1) tRef').
  apply TbValue.
   apply typev_stenv_snoc.
    subst tRef'.
    assert (closedT t2).
     unfold closedT.
     rrwrite (0 = @length ki nil).
     apply (kind_wfT nil t2 KData).

     (* NOTE: This one has to be done manually to instantiate existentials *)
     apply (typex_kind_type nil nil se sp (XVal v1) t2 (TBot KEffect)).
    auto. auto. auto.
     
 assert (Forall2 (TYPEB nil nil (tRef' <: se) sp) ss se).
  lets D: (@Forall2_impl stbind ty) 
                (TYPEB nil nil se sp) 
                (TYPEB nil nil (tRef' <: se) sp)
                ss se H0.
  intros.
  apply typeb_stenv_snoc.
   auto.
   subst tRef'. eauto.
  auto. auto.
Qed.
Hint Resolve storet_snoc.


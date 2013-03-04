
Require Export Iron.SystemF2Effect.Value.
Require Import Iron.SystemF2Effect.Value.TyJudge.WeakStProps.
Require Import Iron.SystemF2Effect.Value.TyJudge.TypeKind.


(* Store bindings are the primitive objects we keep in the store.
   Each one is tagged with the number of the region is in. *)
Inductive stbind :=
 (* A store value in some region. *)
 | StValue : nat -> val -> stbind.
Hint Constructors stbind.

(* A store is a list of store bindings. *)
Definition store := list stbind.


(******************************************************************************)
(* Types of store bindings. *)
Inductive TYPEB : kienv -> tyenv -> stenv -> stprops -> stbind -> ty -> Prop := 
 | TbValue
   :  forall ke te se sp n v t
   ,  TYPEV  ke te se sp v t
   -> TYPEB  ke te se sp (StValue n v) (TRef (TCap (TyCapRegion n)) t).
Hint Constructors TYPEB.


(* Weakening store environment in type of store binding *)
Lemma typeb_stenv_snoc 
 :  forall ke te se sp v t1 t2 
 ,  TYPEB  ke te se sp v t1
 -> ClosedT t2
 -> TYPEB  ke te (t2 <: se) sp v t1.
Proof.
 intros. inverts H. eauto.
Qed.
Hint Resolve typeb_stenv_snoc.


(* Weakening store properties  in type of store binding *)
Lemma typeb_stprops_snoc
 :  forall ke te se sp v t p
 ,  TYPEB  ke te se sp v t
 -> TYPEB  ke te se (p <: sp) v t.
Proof. 
 intros. inverts H. eauto.
Qed.
Hint Resolve typeb_stprops_snoc.


Lemma typeb_stprops_cons
 :  forall ke te se sp v t p
 ,  TYPEB  ke te se sp v t
 -> TYPEB  ke te se (sp :> p) v t.
Proof. 
 intros. inverts H. eauto.
Qed.
Hint Resolve typeb_stprops_snoc.


(******************************************************************************)
(* Well typed store.
   All bindings are well typed. *)
Definition STORET (se: stenv) (sp: stprops) (ss: store)
 := Forall2 (TYPEB nil nil se sp) ss se.
Hint Unfold STORET.


(* Weaken store properties in store typing judgement. *)
Lemma storet_weak_stprops
 :  forall se sp ss p
 ,  STORET se sp ss
 -> STORET se (sp :> SRegion p) ss.
Proof.
 intros.
 unfold STORET in *.
 eapply Forall2_impl.
  intros. eapply typeb_stprops_cons. eauto.
 auto.
Qed.
Hint Resolve storet_weak_stprops.


(* Extended store is well typed under extended store environment *)
Lemma storet_snoc
 :  forall se sp ss r1 v1 t2
 ,  TYPEV  nil nil se sp v1 t2
 -> STORET                                     se  sp                   ss
 -> STORET (TRef (TCap (TyCapRegion r1)) t2 <: se) sp (StValue r1 v1 <: ss).
Proof.
 intros.
 set (tRef' := TRef (TCap (TyCapRegion r1)) t2).

 assert (TYPEB nil nil (tRef' <: se) sp (StValue r1 v1) tRef').
  apply TbValue.
   apply typev_stenv_snoc.
    subst tRef'.
    assert (ClosedT t2).
     rrwrite (0 = @length ki nil).
     apply (kind_wfT nil sp t2 KData).

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



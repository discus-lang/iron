
Require Export Iron.Language.SystemF2Effect.Value.
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Step.FreshF.
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
   ,  (forall m, ~(In (FPriv m n) fs))               (* TODO: change to use freshFs *)
   -> LiveE  fs e2
   -> TYPEF  ke te se sp fs                   t1 t2 e2
   -> TYPEF  ke te se sp (fs :> FPriv None n) t1 t2 e2

 | TfConsExt 
   :  forall ke te se sp fs t0 t1 e2 p1 p2
   ,  In (SRegion p1) sp 
   -> In (SRegion p2) sp
   -> freshFs p2 fs
   -> LiveE  fs (TSum e2 (TAlloc (TRgn p1)))
   -> TYPEF  ke te se sp fs                         (mergeT p1 p2 t0) t1 e2
   -> TYPEF  ke te se sp (fs :> FPriv (Some p1) p2) t0 t1 (TSum e2 (TAlloc (TRgn p1))).

Hint Constructors TYPEF.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_typef :=
 repeat (try 
  (match goal with 
   | [ H: TYPEF _ _ _ _ (_ :> FLet  _ _) _ _ _ |- _ ] => inverts H
   | [ H: TYPEF _ _ _ _ (_ :> FPriv _ _) _ _ _ |- _ ] => inverts H
   end); 
 try inverts_type).


(********************************************************************)
Lemma typef_kind_effect
 :  forall ke te se sp fs t1 t2 e
 ,  TYPEF  ke te se sp fs t1 t2 e
 -> KindT  ke sp e KEffect.
Proof.
 intros.
 induction H; auto.
 - eapply KiSum; eauto.
 - eapply KiSum; auto.
   eapply KiCon1; snorm.
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
 intros. induction H; eauto 2.
Qed.
Hint Resolve typef_kind_t1.


Lemma typef_kind_t2
 :  forall ke te se sp fs t1 t2 e
 ,  TYPEF  ke te se sp fs t1 t2 e
 -> KindT  ke sp t2 KData.
Proof. intros. induction H; auto. Qed.
Hint Resolve typef_kind_t2.


Lemma typef_stenv_snoc
 :  forall ke te se sp fs t1 t2 t3 e
 ,  ClosedT t3
 -> TYPEF ke te se         sp fs t1 t2 e
 -> TYPEF ke te (t3 <: se) sp fs t1 t2 e.
Proof. intros. induction H0; eauto. Qed.
Hint Resolve typef_stenv_snoc.


Lemma typef_stprops_snoc
 :  forall ke te se sp fs t1 t2 p e
 ,  TYPEF  ke te se sp        fs t1 t2 e
 -> TYPEF  ke te se (p <: sp) fs t1 t2 e.
Proof. intros. induction H; eauto. Qed.
Hint Resolve typef_stprops_snoc.


Lemma freshFs_typef
 :  forall ke te se sp fs t1 t2 e p 
 ,  not (In (SRegion p) sp)
 -> TYPEF ke te se sp fs t1 t2 e
 -> freshFs p fs.
Proof.
 intros. gen ke te se sp t1 t2 e.
 induction fs; intros; auto.
 destruct a.
 - inverts H0. 
   eapply freshFs_cons; eauto.
   simpl. rip. eauto.
   admit.                                     (* ok, need typeX_freshX *)
 - inverts H0.
   * eapply freshFs_cons; eauto.
     admit.                                   (* ok, add In (SRegion p) to TsConsPriv *)
   * eapply freshFs_cons; eauto.
     snorm. 
      + admit.                                (* ok, via In. *)
      + admit.                                (* ok, via In. *)
Qed.
Hint Resolve freshFs_typef.



Lemma typef_merge
 :  forall ke te se sp fs t1 t2 e p1 p2
 ,  freshFs     p2 fs
 -> freshFreeFs p2 te fs
 -> TYPEF ke te se sp fs t1 t2 e
 -> TYPEF ke (mergeTE p1 p2 te) (mergeTE p1 p2 se) sp fs t1 t2 e.
Proof.
 intros. gen ke te se sp t1 t2 e.
 induction fs; intros.

 Case "nil".
 { inverts H1. eauto.  
 }

 Case "cons".
 { destruct a.

   - SCase "FLet".
     have (freshFs p2 fs). rip.

     have HF: (freshF  p2 (FLet t e0))
      by (eapply freshFs_tail; eauto).
     unfold freshF in HF. rip. 

     inverts H1.
     eapply TfConsLet; auto.
     + rewrite mergeTE_rewind; auto.
       eapply mergeX_typeX_freshX; eauto.
       * admit.                                  (* ok, fresh join *)
     + eapply IHfs; auto.
       admit.                                    (* ok, freshFree tail *)

   - SCase "FPriv".
     inverts H1.
     * eapply TfConsPriv; auto.
       eapply IHfs; eauto.
       admit.                                    (* ok, freshFree tail *)

     * eapply TfConsExt; eauto.
       eapply IHfs; eauto.
       admit.                                    (* ok, freshFree tail *)
 }
Qed.


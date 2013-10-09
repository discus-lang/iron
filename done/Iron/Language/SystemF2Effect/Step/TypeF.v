
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
   ,  not (In (FPriv n) fs)
   -> LiveE  fs e2
   -> TYPEF  ke te se  sp fs              t1 t2 e2
   -> TYPEF  ke te se  sp (fs :> FPriv n) t1 t2 e2

 | TfConsExt 
   :  forall ke te se sp fs t0 t1 e2 p1 p2
   ,  In (SRegion p1) sp 
   -> In (SRegion p2) sp
   -> freshT  p2 t0      
    -> freshFs p2 fs
   -> KindT  (ke :> KRegion) sp t0 KData
   -> TYPEF  ke te se sp fs 
                         (substTT 0 (TRgn p1) t0) t1 e2
   -> TYPEF  ke te se sp (fs :> FExt p1 p2) 
                         (substTT 0 (TRgn p2) t0) t1 (TSum e2 (TAlloc (TRgn p1))).

Hint Constructors TYPEF.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_typef :=
 repeat (try 
  (match goal with 
   | [ H: TYPEF _ _ _ _ (_ :> FLet  _ _) _ _ _ |- _ ] => inverts H
   | [ H: TYPEF _ _ _ _ (_ :> FPriv _)   _ _ _ |- _ ] => inverts H
   | [ H: TYPEF _ _ _ _ (_ :> FExt  _ _) _ _ _ |- _ ] => inverts H
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
 intros.
 induction H; auto.
 - eapply subst_type_type; eauto.
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
 intros. 
 induction H0; eauto.
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
   admit.                        (* ok, need typeX_freshX *)
 - inverts H0.
   eapply freshFs_cons; eauto.
   admit.                        (* ok, add In (SRegion p) to TsConsPriv *)
 - inverts H0.
   eapply freshFs_cons; eauto.
   snorm.
   + admit.                      (* ok, via In. *)
   + admit.                      (* ok, via In. *)
Qed.
Hint Resolve freshFs_typef.


Lemma mergeTE_rewind
 :  forall p1 p2 te t
 ,  freshT p2 t
 -> mergeTE p1 p2 te :> t
 =  mergeTE p1 p2 (te :> t).
Proof.
 intros.

 have HT1: (t = mergeT p1 p2 t)
  by (symmetry; apply mergeT_freshT_id; auto).
 rewrite HT1 at 1.
 snorm.
Qed.


Lemma typex_merge
 :  forall ke te se sp x t e p1 p2
 ,  freshX     p2 x
 -> freshFreeX p2 te x
 -> TYPEX ke te se sp x t e
 -> TYPEX ke (mergeTE p1 p2 te) (mergeSE p1 p2 se) sp x t e.
Proof.
 intros. gen ke te se sp t e.
 induction x using exp_mutind with
  (PV := fun v => forall ke te se sp t 
      ,  freshV     p2 v
      -> freshFreeV p2 te v
      -> TYPEV ke te se sp v t
      -> TYPEV ke (mergeTE p1 p2 te) (mergeSE p1 p2 se) sp v t);
  intros; inverts_type; auto.

 - Case "XVar".
   eapply TvVar; auto.
   unfold freshFreeV in *.
   spec H1 n. spec H1 t.

   have HF: (freeXV n (VVar n)) 
    by (unfold freeXV; symmetry; eapply beq_nat_refl).

   assert (freshT p2 t).
    eauto. clear H1.

   unfold mergeTE.
   eapply get_map with (f := mergeT p1 p2) in H4.
   rewrite H4.
   rewrite mergeT_freshT_id; auto.

 - Case "XLoc".
   eapply TvLoc; auto.
   admit.                               (* ok, need freshSuppV crap *)

 - Case "XLam".
   eapply TvLam; auto.
   snorm. rewrite mergeTE_rewind; auto.
   eapply IHx; auto.
   + admit.

 - Case "XLAM".
   eapply TvLAM. admit.

 - Case "XLet".
   snorm.
   eapply TxLet; auto.
   + eapply IHx1; auto. firstorder.
   + rewrite mergeTE_rewind.
     eapply IHx2; auto. admit. admit.
 
 - Case "XApp".
   snorm.
   eapply TxApp. 
   + eapply IHx; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H0; snorm; eauto.
   + eapply IHx0; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H0; snorm; eauto.

 - Case "XAPP".
   admit.

 - Case "XOp1".
   eapply TxOpPrim; eauto.

 - Case "XPrivate".
   eapply TxPrivate; eauto.
   admit.                             (* ok, comm liftTE/mergeTE *)

 - Case "XExtend".
   eapply TxExtend; eauto.
   admit.                             (* ok, comm liftTE/mergeTE *)

 - Case "XAlloc".
   eapply TxOpAlloc; eauto.
   + eapply IHx; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H; snorm; eauto.

 - Case "XRead".
   eapply TxOpRead; eauto.
   + eapply IHx; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H; snorm; eauto.

 - Case "XWrite".
   eapply TxOpWrite; eauto.
   + eapply IHx; snorm; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H0; snorm; eauto.
   + eapply IHx0; snorm; eauto.
     unfold freshFreeX in *.
     unfold freshFreeV in *.
     intros. rip. eapply H0; snorm; eauto.
Qed.



Lemma typef_merge
 :  forall ke te se sp fs t1 t2 e p1 p2
 ,  freshFs     p2 fs
 -> freshFreeFs p2 te fs
 -> TYPEF ke te se sp fs t1 t2 e
 -> TYPEF ke (mergeTE p1 p2 te) (mergeSE p1 p2 se) sp fs t1 t2 e.
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
       eapply typex_merge; eauto.
       * admit.                                  (* ok, fresh join *)
     + eapply IHfs; auto.
       admit.                                    (* ok, freshFree tail *)

   - SCase "FPriv".
     inverts H1.
     eapply TfConsPriv; auto.
     eapply IHfs; eauto.
     admit.                                      (* ok, freshFree tail *)

   - SCase "FExt".
     inverts H1.
     eapply TfConsExt; auto.
     eapply IHfs; eauto.
     admit.                                      (* ok, freshFree tail *)
 }
Qed.



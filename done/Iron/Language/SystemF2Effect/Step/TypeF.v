
Require Export Iron.Language.SystemF2Effect.Value.
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Step.FreshF.
Require Export Iron.Language.SystemF2Effect.Step.SuppF.
Require Export Iron.Language.SystemF2Effect.Store.
Require Export Iron.Language.SystemF2Effect.Store.LiveE.


(********************************************************************)
(* Type of a frame stack.
   The frame stack is like a continuation that takes an expression of
   a certain type and produces a new expression. *)
Inductive
 TypeF :  kienv -> tyenv 
       -> stenv -> stprops 
       -> stack -> ty -> ty 
       -> ty -> Prop := 
 | TfNil 
   :  forall ke te se sp t
   ,  KindT  ke sp t KData
   -> TypeF  ke te se sp nil t t (TBot KEffect)

 | TfConsLet
   :  forall ke te se sp fs t1 x2 t2 e2 t3 e3
   ,  KindT  ke sp t1 KData
   -> TypeX  ke (te :> t1) se sp                    x2 t2 e2
   -> TypeF  ke te         se sp fs                 t2 t3 e3
   -> TypeF  ke te         se sp (fs :> FLet t1 x2) t1 t3 (TSum e2 e3)

 | TfConsPriv
   :  forall ke te se sp fs t1 t2 e2 p
   ,  In (SRegion p) sp
   -> NoPrivFs p fs
   -> LiveE  fs e2
   -> TypeF  ke te se sp fs                   t1 t2 e2
   -> TypeF  ke te se sp (fs :> FPriv None p) t1 t2 e2

 | TfConsExt 
   :  forall ke te se sp fs t0 t1 e2 p1 p2
   ,  In (SRegion p1) sp 
   -> In (SRegion p2) sp
   -> FreshFs     p2 fs
   -> FreshSuppFs p2 se fs
   -> LiveE  fs (TSum e2 (TAlloc (TRgn p1)))
   -> TypeF  ke te se sp fs                         (mergeT p1 p2 t0) t1 e2
   -> TypeF  ke te se sp (fs :> FPriv (Some p1) p2) t0 t1 (TSum e2 (TAlloc (TRgn p1))).

Hint Constructors TypeF.


(* Invert all hypothesis that are compound typing statements. *)
Ltac inverts_typef :=
 repeat (try 
  (match goal with 
   | [ H: TypeF _ _ _ _ (_ :> FLet  _ _) _ _ _ |- _ ] => inverts H
   | [ H: TypeF _ _ _ _ (_ :> FPriv _ _) _ _ _ |- _ ] => inverts H
   end); 
 try inverts_type).


(********************************************************************)
Lemma typeF_kindT_effect
 :  forall ke te se sp fs t1 t2 e
 ,  TypeF  ke te se sp fs t1 t2 e
 -> KindT  ke sp e KEffect.
Proof.
 intros.
 induction H; auto.
 - eapply KiSum; eauto.
 - eapply KiSum; auto.
   eapply KiCon1; snorm.
Qed.
Hint Resolve typeF_kindT_effect.


Lemma typeF_kindT_wfT
 :  forall ke te se sp fs t1 t2 e
 ,  TypeF  ke te se sp fs t1 t2 e
 -> WfT (length ke) e.
Proof. eauto. Qed.
Hint Resolve typeF_kindT_wfT.


Lemma typeF_kindT_t1
 :  forall ke te se sp fs t1 t2 e
 ,  TypeF  ke te se sp fs t1 t2 e
 -> KindT  ke sp t1 KData.
Proof. 
 intros. induction H; eauto 2.
Qed.
Hint Resolve typeF_kindT_t1.


Lemma typeF_kindT_t2
 :  forall ke te se sp fs t1 t2 e
 ,  TypeF  ke te se sp fs t1 t2 e
 -> KindT  ke sp t2 KData.
Proof. intros. induction H; auto. Qed.
Hint Resolve typeF_kindT_t2.


(********************************************************************)
Lemma typeF_coversFs
 :  forall ke te se sp fs t1 t2 e
 ,  TypeF  ke te se sp fs t1 t2 e
 -> CoversFs se fs.
Proof.
 intros. gen ke te se sp t1 t2 e.
 induction fs as [|f]; intros.
 - eauto.
 - eapply Forall_cons; eauto.
   + inverts H.
     * eapply typeX_coversX; eauto.
     * unfold CoversF; snorm.
     * unfold CoversF; snorm.
   + inverts H; eapply IHfs; eauto.
Qed.


Lemma typeF_stenv_snoc
 :  forall ke te se sp fs t1 t2 t3 e
 ,  ClosedT t3
 -> TypeF ke te se         sp fs t1 t2 e
 -> TypeF ke te (t3 <: se) sp fs t1 t2 e.
Proof. 
 intros.
 induction H0; eauto. 

 - eapply TfConsExt; auto.
   eapply freshSuppFs_coveredFs.
   eapply typeF_coversFs; eauto. auto.
Qed.  
Hint Resolve typeF_stenv_snoc.


Lemma typeF_stprops_snoc
 :  forall ke te se sp fs t1 t2 p e
 ,  TypeF  ke te se sp        fs t1 t2 e
 -> TypeF  ke te se (p <: sp) fs t1 t2 e.
Proof. intros. induction H; eauto. Qed.
Hint Resolve typeF_stprops_snoc.


Lemma typeF_freshFs
 :  forall ke te se sp fs t1 t2 e p 
 ,  not (In (SRegion p) sp)
 -> TypeF ke te se sp fs t1 t2 e
 -> FreshFs p fs.
Proof.
 intros. gen ke te se sp t1 t2 e.
 induction fs; intros; auto.
 destruct a.
 - inverts H0. 
   eapply freshFs_cons; eauto.
   simpl. rip. eauto.
   eapply freshX_typeX; eauto.
 - inverts H0.
   * eapply freshFs_cons; eauto.
     lets D: (@in_not_in stprop) H4 H.
     have (p <> n) by congruence.
     simpl. auto.
    * eapply freshFs_cons; eauto.
     snorm. 
      + lets D: (@in_not_in stprop) H5 H.
        congruence.
      + lets D: (@in_not_in stprop) H5 H.
        congruence.
Qed.
Hint Resolve typeF_freshFs.


Lemma typeF_freshSuppFs
 :  forall ke te se sp fs t1 t2 e p
 ,  not (In (SRegion p) sp)
 -> TypeF ke te se sp fs t1 t2 e
 -> FreshSuppFs p se fs.
Proof.
 intros. gen ke te se sp t1 t2 e.
 induction fs as [|f]; intros; auto.
 eapply Forall_cons; auto.
 - clear IHfs.
   destruct f; snorm; inverts H0.
   + simpl.
     eapply freshSuppX_typeX; eauto.
 - inverts H0; eapply IHfs; eauto.
Qed.


Lemma typeF_allocRegion_noprivFs
 : forall ke te se sp fs t1 t2 e p
 ,  p = allocRegion sp
 -> TypeF ke te se sp fs t1 t2 e
 -> NoPrivFs p fs.
Proof.
 intros.
 eapply freshFs_noprivFs.
 eapply typeF_freshFs.
 lets D: allocRegion_fresh sp.
 rewrite <- H in D. eauto. eauto.
Qed.
Hint Resolve typeF_allocRegion_noprivFs. 


Lemma typeF_mergeTE
 :  forall ke te se sp fs t1 t2 e p1 p2
 ,  FreshFs     p2 fs
 -> FreshFreeFs p2 te fs
 -> FreshSuppFs p2 se fs
 -> TypeF ke te se sp fs t1 t2 e
 -> TypeF ke (mergeTE p1 p2 te) (mergeTE p1 p2 se) sp fs t1 t2 e.
Proof.
 intros. gen ke te se sp t1 t2 e. gen p1 p2.
 induction fs as [|f]; intros.

 Case "nil".
 { inverts H2. eauto.  
 }

 Case "cons".
 { destruct f.

   - SCase "FLet".
     have (FreshFs p2 fs). rip.

     have HF: (FreshF  p2 (FLet t e0))
      by (eapply freshFs_tail; eauto).
     unfold FreshF in HF. rip. 

     inverts H2.
     eapply TfConsLet; auto.
     + rewrite mergeTE_rewind; auto.
       eapply mergeX_typeX_freshX; eauto.
       * inverts H0; snorm.
       * inverts H1; snorm.
     + eapply IHfs; eauto.

   - SCase "FPriv".
     inverts H2.
     * eapply TfConsPriv; auto.
       eapply IHfs; eauto. 
     * eapply TfConsExt; eauto.
       have (FreshSuppFs p2 se fs).
       eapply freshSuppFs_mergeTE; auto.     
 }
Qed.


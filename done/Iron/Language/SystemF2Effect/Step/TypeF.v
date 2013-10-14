
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
   :  forall ke te se sp fs t1 t2 e2 p
   ,  In (SRegion p) sp
   -> noprivFs p fs
   -> LiveE  fs e2
   -> TYPEF  ke te se sp fs                   t1 t2 e2
   -> TYPEF  ke te se sp (fs :> FPriv None p) t1 t2 e2

 | TfConsExt 
   :  forall ke te se sp fs t0 t1 e2 p1 p2
   ,  In (SRegion p1) sp 
   -> In (SRegion p2) sp
   -> freshFs     p2 fs
   -> freshSuppFs p2 se fs
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

(*
Lemma typef_stenv_snoc
 :  forall ke te se sp fs t1 t2 t3 e
 ,  ClosedT t3
 -> TYPEF ke te se         sp fs t1 t2 e
 -> TYPEF ke te (t3 <: se) sp fs t1 t2 e.
Proof. 
 intros.
 induction H0; eauto. 
 
 - eapply TfConsExt; auto.

Hint Resolve typef_stenv_snoc.
*)

Lemma typef_stprops_snoc
 :  forall ke te se sp fs t1 t2 p e
 ,  TYPEF  ke te se sp        fs t1 t2 e
 -> TYPEF  ke te se (p <: sp) fs t1 t2 e.
Proof. intros. induction H; eauto. Qed.
Hint Resolve typef_stprops_snoc.


Lemma freshFs_typeF
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
   eapply freshX_typeX; eauto.
 - inverts H0.
   * eapply freshFs_cons; eauto.
     lets D: (@in_not_in stprop) H4 H.
     have (p <> n) by congruence.
     simpl.
     rewrite beq_nat_false_iff.
     auto.   
    * eapply freshFs_cons; eauto.
     snorm. 
      + lets D: (@in_not_in stprop) H5 H.
        have (p1 <> p) by congruence.
        rewrite beq_nat_false_iff. 
        auto.
      + lets D: (@in_not_in stprop) H5 H.
        have (p <> n) by congruence.
        rewrite beq_nat_false_iff.
        auto.
Qed.
Hint Resolve freshFs_typeF.


Lemma freshF_noprivF
 : forall p f
 , freshF p f -> noprivF p f.
Proof.
 intros.
 destruct f.
 - snorm.
 - destruct o; snorm.
Qed.
Hint Resolve freshF_noprivF. 


Lemma freshFs_noprivFs
 : forall  p fs
 , freshFs p fs -> noprivFs p fs.
Proof.
 intros.
 induction fs.
 - unfold noprivFs. eauto.
 - unfold noprivFs. inverts H. firstorder.
Qed.
Hint Resolve freshFs_noprivFs.


Lemma typeF_allocRegion_noprivFs
 : forall ke te se sp fs t1 t2 e p
 ,  p = allocRegion sp
 -> TYPEF ke te se sp fs t1 t2 e
 -> noprivFs p fs.
Proof.
 intros.
 eapply freshFs_noprivFs.
 eapply freshFs_typeF.
 lets D: allocRegion_fresh sp.
 rewrite <- H in D. eauto. eauto.
Qed.
Hint Resolve typeF_allocRegion_noprivFs. 



Lemma freshSuppF_mergeTE
 :  forall p1 p2 p3 te f
 ,  freshSuppF p1 te f
 -> freshSuppF p2 te f
 -> freshSuppF p2 (mergeTE p3 p1 te) f.
Proof.
 intros.
 destruct f.
 - snorm.
   eapply freshSuppX_mergeTE; auto.
 - eauto. 
Qed.



Lemma freshSuppFs_mergeTE
 :  forall p1 p2 p3 te fs
 ,  freshSuppFs p1 te fs
 -> freshSuppFs p2 te fs
 -> freshSuppFs p2 (mergeTE p3 p1 te) fs.
Proof.
 intros.
 unfold freshSuppFs in *.
 induction fs; auto.
 inverts H.
 inverts H0. rip.
 eapply Forall_cons; auto.
 eapply freshSuppF_mergeTE; auto.
Qed.


Lemma typeF_mergeTE
 :  forall ke te se sp fs t1 t2 e p1 p2
 ,  freshFs     p2 fs
 -> freshFreeFs p2 te fs
 -> freshSuppFs p2 se fs
 -> TYPEF ke te se sp fs t1 t2 e
 -> TYPEF ke (mergeTE p1 p2 te) (mergeTE p1 p2 se) sp fs t1 t2 e.
Proof.
 intros. gen ke te se sp t1 t2 e. gen p1 p2.
 induction fs as [|f]; intros.

 Case "nil".
 { inverts H2. eauto.  
 }

 Case "cons".
 { destruct f.

   - SCase "FLet".
     have (freshFs p2 fs). rip.

     have HF: (freshF  p2 (FLet t e0))
      by (eapply freshFs_tail; eauto).
     unfold freshF in HF. rip. 

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
       have (freshSuppFs p2 se fs).
       eapply freshSuppFs_mergeTE; auto.     
 }
Qed.


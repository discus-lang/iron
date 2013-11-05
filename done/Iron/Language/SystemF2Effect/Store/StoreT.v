
Require Export Iron.Language.SystemF2Effect.Store.Bind.
Require Export Iron.Language.SystemF2Effect.Store.TypeB.

(********************************************************************)
(* Well typed store.
   All bindings are well typed. *)
Definition StoreT' (sec : stenv) (se: stenv) (sp: stprops) (ss: store)
 := Forall2 (TypeB nil nil sec sp) ss se.
Hint Unfold StoreT'.

Definition StoreT  (se  : stenv) (sp : stprops) (ss : store)
 := StoreT' se se sp ss.
Hint Unfold StoreT.


(********************************************************************)
Lemma storeT_mergeB
 :  forall  sec se sp ss p1 p2
 ,  In (SRegion p1) sp
 -> StoreT' sec se sp ss
 -> StoreT' (mergeTE p1 p2 sec) (mergeTE p1 p2 se) sp (mergeBs p1 p2 ss).
Proof.
 intros.
 unfold StoreT' in *.
 induction H0.
 - snorm.
 - simpl. eapply Forall2_cons.
   + rgwrite (nil = mergeTE p1 p2 nil).
     eapply typeB_mergeT. auto. auto.
   + auto.
Qed.


(* Weaken store properties in store typing judgement. *)
Lemma storeT_weak_stprops
 :  forall se sp ss p
 ,  StoreT se sp ss
 -> StoreT se (SRegion p <: sp) ss.
Proof.
 intros.
 unfold StoreT in *.
 eapply Forall2_impl.
 - intros. eapply typeB_stprops_snoc. eauto.
 - auto.
Qed.
Hint Resolve storeT_weak_stprops.


(* All region handles in store bindings are present 
   in the store properties. *)
Lemma storeT_handles_in_stprops
 :  forall se sp ss
 ,  StoreT se sp ss
 -> Forall (fun s => forall p
                  ,  regionOfStBind s = p 
                  -> In (SRegion p) sp) 
           ss.
Proof.
 intros.
 snorm.
 unfold StoreT in *.
 have (exists ix, get ix ss = Some x).
  dest ix.
 have (exists t, TypeB nil nil se sp x t).
  dest t.
 inverts H3.
 - snorm. subst. inverts_kind. auto.
 - snorm. subst. inverts_kind. auto.
Qed.



(* Extended store is well typed under extended store environment *)
Lemma storeT_snoc
 :  forall se sp ss p1 v1 t2
 ,  In (SRegion p1) sp
 -> TypeV  nil nil se sp v1 t2
 -> StoreT                       se  sp                   ss
 -> StoreT (TRef (TRgn p1) t2 <: se) sp (StValue p1 v1 <: ss).
Proof.
 intros.
 set (tRef' := TRef (TRgn p1) t2).

 assert (TypeB nil nil (tRef' <: se) sp (StValue p1 v1) tRef').
 { apply TbValue; auto.
   - apply typev_stenv_snoc.
     subst tRef'.
     assert (ClosedT t2).
      rrwrite (0 = @length ki nil).
      apply (kind_wfT nil sp t2 KData).

      (* NOTE: This one has to be done manually to instantiate existentials *)
      apply (typex_kind_type nil nil se sp (XVal v1) t2 (TBot KEffect)).
       auto. auto. auto.
 }

 assert (Forall2 (TypeB nil nil (tRef' <: se) sp) ss se).
 { lets D: (@Forall2_impl stbind ty) 
                (TypeB nil nil se sp) 
                (TypeB nil nil (tRef' <: se) sp)
                ss se H1.
   intros.
   apply typeB_stenv_snoc. auto. subst tRef'. eauto.
   auto.
 }

 unfold StoreT.
 auto.
Qed.
Hint Resolve storeT_snoc.


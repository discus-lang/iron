
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(******************************************************************************)
(* Types of store bindings. *)
Inductive TypeB : kienv -> tyenv -> stenv -> stprops -> stbind -> ty -> Prop := 
 (* A store binding that contains a live value.
    Requiring that the region handle is well kinded ensures that it's 
    mentioned in the store properties. *)
 | TbValue
   :  forall ke te se sp p v t
   ,  In (SRegion p) sp
   -> TypeV  ke te se sp v t
   -> TypeB  ke te se sp (StValue p v) (TRef (TRgn p) t)

 (* After a store binding has been dealloated,
    we can treat the location has having any type we want.
    The progress theorem guarantees these dead bindings will never be read,
    so there is no opportunity to treat it has having the wrong type. *)
 | TbDead 
   :  forall ke te se sp p t
   ,  In (SRegion p) sp
   -> TypeB  ke te se sp (StDead p)    (TRef (TRgn p) t).

Hint Constructors TypeB.


(******************************************************************************)
(* Weakening store environment in type of store binding *)
Lemma typeB_stenv_snoc 
 :  forall ke te se sp v t1 t2 
 ,  TypeB  ke te se sp v t1
 -> ClosedT t2
 -> TypeB  ke te (t2 <: se) sp v t1.
Proof.
 intros. 
 inverts H; eauto.
Qed.
Hint Resolve typeB_stenv_snoc.


(* Weakening store properties  in type of store binding *)
Lemma typeB_stprops_snoc
 :  forall ke te se sp v t p
 ,  TypeB  ke te se sp v t
 -> TypeB  ke te se (p <: sp) v t.
Proof. 
 intros. 
 inverts H; eauto using kind_stprops_snoc.
Qed.
Hint Resolve typeB_stprops_snoc.


Lemma typeB_stprops_cons
 :  forall ke te se sp v t p
 ,  TypeB  ke te se sp v t
 -> TypeB  ke te se (sp :> p) v t.
Proof. 
 intros.
 inverts H; eauto using kind_stprops_cons.
Qed.
Hint Resolve typeB_stprops_snoc.


Lemma typeB_mergeT
 :  forall ke te se sp b t p1 p2
 ,  In (SRegion p1) sp
 -> TypeB  ke te se sp b t
 -> TypeB  ke (mergeTE p1 p2 te) (mergeTE p1 p2 se) sp 
              (mergeB p1 p2 b) (mergeT p1 p2 t).
Proof.
 intros.
 destruct b.

 Case "StValue".
 { have (p2 = n \/ ~(p2 = n)) as HN.
   inverts HN.
   - inverts H0.
     + snorm; subst.
       * eapply TbValue; eauto.
         eapply TxVal in H9.
         eapply mergeX_typeX in H9.
         inverts H9. eauto.
         inverts_kind. auto.
       * nope.
   - inverts H0.
     + snorm; subst.
       * nope.
       * eapply TbValue; eauto.
         eapply TxVal in H10.
         eapply mergeX_typeX in H10.
         inverts H10. eauto. auto.
 }

 Case "StDead". 
 { have (p2 = n \/ ~(p2 = n)) as HN.
   inverts HN.
   - inverts H0.
     snorm.
   - inverts H0.
     snorm.
 }
Qed.

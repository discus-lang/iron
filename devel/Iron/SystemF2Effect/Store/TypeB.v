
Require Export Iron.SystemF2Effect.Store.Bind.


(******************************************************************************)
(* Types of store bindings. *)
Inductive TYPEB : kienv -> tyenv -> stenv -> stprops -> stbind -> ty -> Prop := 
 (* A store binding that contains a live value.
    Requiring that the region handle is well kinded ensures that it's 
    mentioned in the store properties. *)
 | TbValue
   :  forall ke te se sp n v t
   ,  KindT  ke sp (TCap (TyCapRegion n)) KRegion
   -> TYPEV  ke te se sp v t
   -> TYPEB  ke te se sp (StValue n v) (TRef (TCap (TyCapRegion n)) t)

 (* After a store binding has been dealloated,
    we can treat the location has having any type we want.
    The progress theorem guarantees these dead bindings will never be read,
    so there is no opportunity to treat it has having the wrong type. *)
 | TbDead 
   :  forall ke te se sp n t
   ,  KindT  ke sp (TCap (TyCapRegion n)) KRegion
   -> TYPEB  ke te se sp (StDead n)    (TRef (TCap (TyCapRegion n)) t).

Hint Constructors TYPEB.


(* Weakening store environment in type of store binding *)
Lemma typeb_stenv_snoc 
 :  forall ke te se sp v t1 t2 
 ,  TYPEB  ke te se sp v t1
 -> ClosedT t2
 -> TYPEB  ke te (t2 <: se) sp v t1.
Proof.
 intros. 
 inverts H; eauto.
Qed.
Hint Resolve typeb_stenv_snoc.


(* Weakening store properties  in type of store binding *)
Lemma typeb_stprops_snoc
 :  forall ke te se sp v t p
 ,  TYPEB  ke te se sp v t
 -> TYPEB  ke te se (p <: sp) v t.
Proof. 
 intros. 
 inverts H; eauto using kind_stprops_snoc.
Qed.
Hint Resolve typeb_stprops_snoc.


Lemma typeb_stprops_cons
 :  forall ke te se sp v t p
 ,  TYPEB  ke te se sp v t
 -> TYPEB  ke te se (sp :> p) v t.
Proof. 
 intros.
 inverts H; eauto using kind_stprops_cons.
Qed.
Hint Resolve typeb_stprops_snoc.

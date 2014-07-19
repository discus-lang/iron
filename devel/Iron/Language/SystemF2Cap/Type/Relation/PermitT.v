
Require Import Iron.Language.SystemF2Cap.Type.Exp.
Require Import Iron.Language.SystemF2Cap.Type.TyEnv.
Require Import Iron.Language.SystemF2Cap.Type.Util.
Require Import Iron.Language.SystemF2Cap.Type.Operator.FlattenT.
Require Import Iron.Language.SystemF2Cap.Type.Operator.SubstTT.

(* Atomic effect is permitted by a capability in the type environment. *)
Definition PermitT_atomic (ke : kienv) (te : tyenv) (e : ty) 
 := forall n
 ,  varOfEffect e = Some n
 -> (get n ke  = Some (OCon, KRegion) /\ In e te)
 \/ (get n ke  = Some (OAbs, KRegion)).

(* All atomic effect in this list are permitted by capabilities in
   the type environment. *)
Definition PermitT_list   (ke : kienv) (te : tyenv) (es : list ty)
 := Forall (PermitT_atomic ke te)  es.

(* Effect is permitted by the type environment. *)
Definition PermitT        (ke : kienv) (te : tyenv) (e : ty)
 := PermitT_list ke te (flattenT e).

(*
Lemma permitsT_subst_exp_ix_atomic
 :  forall ix ke te t e o2 k2
 ,  get ix ke = Some (o2, k2)
 -> PermitsT_atomic ke te e
 -> PermitsT_atomic (delete ix ke) (substTE ix t te) (substTT ix t e).
Proof.
 unfold PermitsT_atomic.
 intros.
 intros.


Lemma permitsT_subst_exp_ix
 : forall ix ke te t e o2 k2
 ,  get ix ke = Some (o2, k2)
 -> PermitsT ke te e
 -> PermitsT (delete ix ke) (substTE ix t te) (substTT ix t e).
Proof.
 unfold PermitsT.
 unfold PermitsT_list.
 snorm.

 lets D: H0 x.
*)
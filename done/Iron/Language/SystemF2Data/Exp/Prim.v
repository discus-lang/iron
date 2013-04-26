
Require Import Iron.Language.SystemF2Data.Type.
Require Import Iron.Language.SystemF2Data.Exp.Lit.


(********************************************************************)
(* Primive operatos. *)
Inductive prim : Type :=
 (* Add two naturals. *)
 | PAdd    : prim

 (* Check whether a natural is zero. *)
 | PIsZero : prim.


(* Primitive operator definition.
   We keep the types of primops separate from the main typing judgement
   to make it easy to add new ones. *)
Inductive defprim : Type :=
 | DefPrim 
   :  list ty    (* Types of the arguments. *)
   -> ty         (* Type  of the returned value. *)
   -> defprim.


(* Define the types of primops. *)
Fixpoint primDef (p : prim) : defprim := 
 match p with
 | PAdd      => DefPrim (TCon TyConNat :: TCon TyConNat :: nil) (TCon TyConNat)
 | PIsZero   => DefPrim (TCon TyConNat :: nil)                  (TCon TyConBool)
 end. 


(********************************************************************)
(* The types of all primops are closed. *)
Lemma prim_types_closed
 :   forall p ts t
 ,   primDef p = DefPrim ts t
 ->  Forall closedT ts
  /\ closedT t.
Proof.
 intro.
 destruct p; snorm;
  try (solve [inverts H; nope]);
  try (solve [inverts H; eauto]).

 + inverts H.
   inverts H0. eauto.
   inverts H.  eauto.
   nope.

 + inverts H.
   inverts H0. eauto.
   inverts H.
Qed.
Hint Resolve prim_types_closed.


Lemma prim_types_closed_args
 :  forall p ts t
 ,  primDef p = DefPrim ts t
 -> Forall closedT ts.
Proof.
 intros. eapply prim_types_closed in H; rip.
Qed.
Hint Resolve prim_types_closed_args.


Lemma prim_types_closed_result
 :  forall p ts t
 ,  primDef p = DefPrim ts t
 -> closedT t.
Proof.
 intros. eapply prim_types_closed in H; rip.
Qed.
Hint Resolve prim_types_closed_result.



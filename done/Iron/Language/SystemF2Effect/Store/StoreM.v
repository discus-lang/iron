
Require Export Iron.Language.SystemF2Effect.Step.Frame.
Require Export Iron.Language.SystemF2Effect.Store.Bind.


(* Store typing models the store.
   All types in the store typing have a corresponding binding in the store.
   We don't want entries in the store typing that don't have corresponding
   bindings in the store. *)

Definition STOREM (se: stenv) (ss: store)
 := length se = length ss.
Hint Unfold STOREM.


(* Extended store environment models the extended store *)
Lemma storem_snoc
 :  forall se ss t stv
 ,  STOREM se ss
 -> STOREM (t <: se) (stv <: ss).
Proof.
 intros.
 unfold STOREM.
 have (length se = length ss). 
 burn.
Qed.
Hint Resolve storem_snoc.

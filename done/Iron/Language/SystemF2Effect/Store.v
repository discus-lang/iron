
Require Export Iron.Language.SystemF2Effect.Store.Wf.
Require Export Iron.Language.SystemF2Effect.Store.TypeB.
Require Export Iron.Language.SystemF2Effect.Store.StoreT.
Require Export Iron.Language.SystemF2Effect.Store.LiveE.
Require Export Iron.Language.SystemF2Effect.Store.LiveS.


(* Reading bindings **********************************************************)
(* Values read from the store have the types predicted by
   the store environment *)
Lemma storet_get_typev
 :  forall se sp ss ix r v t
 ,  StoreT se sp ss
 -> get ix se = Some (TRef (TRgn r) t)
 -> get ix ss = Some (StValue r v)
 -> TypeV nil nil se sp v t.
Proof.
 intros.
 unfold StoreT in *.
 lets D: (@Forall2_get_get_same stbind ty) H1 H0. eauto.
 inverts D. auto.
Qed.


Require Export Iron.SystemF2Effect.Step.TypeC.
Require Export Iron.SystemF2Effect.Type.Operator.FreeTT.
Require Export Iron.SystemF2Effect.Store.LiveS.
Require Export Iron.SystemF2Effect.Store.LiveE.


(* Similar store bindings.
   Two bindings are similar if the second is dead, 
   or they are both in the same region and hold the same value. *)
Inductive SimStBind : stbind -> stbind -> Prop :=
 | SimDead 
   :  forall b1 b2 p
   ,  b2 = StDead p
   -> SimStBind b1 b2

 | SimValue
   :  forall b1 b2 p v
   ,  b1 = StValue p v
   -> b2 = StValue p v
   -> SimStBind b1 b2.


Theorem stepWrite 
 :  forall se  sp  ss fs x   ss' sp' fs' x' t e p
 ,  TYPEC  nil nil se sp fs  x   t   e
 -> STEPF  ss  sp  fs x  ss' sp' fs' x' 
 -> not (In (TWrite (TRgn p)) (flattenT e))
 -> Forall2 (fun b1 b2 => regionOfStBind b1 = p -> SimStBind b1 b2)
            ss ss'.
Proof.
 intros.

 (* say second store extends the other, and the existing values are related. *)

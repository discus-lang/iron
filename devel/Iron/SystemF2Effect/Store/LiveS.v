
Require Export Iron.SystemF2Effect.Step.Frame.
Require Export Iron.SystemF2Effect.Store.Bind.
Require Export Iron.SystemF2Effect.Store.LiveE.


Definition isFUse    (p : nat) (f : frame)
 := f = FUse p.
Hint Unfold isFUse.


Definition isStValue (b : stbind)
 := exists p v, b = StValue p v.
Hint Unfold isStValue.


Definition regionOfStBind (b : stbind)
 := match b with 
    | StValue n _ => n
    | StDead  n   => n
    end.
Hint Unfold regionOfStBind.


Definition LiveF (ss : store) (f : frame)
 := forall p, isFUse p f 
           -> Forall (fun b => regionOfStBind b = p
                            -> isStValue b) 
                      ss.

Definition LiveS  (ss : store) (fs : stack)
 := Forall (LiveF ss) fs.
                         


Lemma liveS_liveE_value
 :  forall ss fs e l b p
 ,  LiveS ss fs
 -> LiveE fs e
 -> handleOfEffect e = Some p
 -> get l ss         = Some b
 -> regionOfStBind b = p
 -> exists v, b = StValue p v.
Proof.
 intros ss fs e l b p HLS HLE. intros.

 destruct b.
 - snorm. subst. exists v. eauto.
 - have HIF: (In (FUse p) fs) 
    by  (eapply liveE_fUse_in; eauto; snorm).

   unfold LiveS in HLS.
   unfold LiveF in HLS.
   snorm.
 
   eapply HLS with (p := n) in HIF.
   + snorm.
     have (In (StDead n) ss) as HD. subst.
     eapply HIF in HD.
     unfold isStValue in HD. nope.
     snorm.
   + snorm.
Qed.


Lemma liveS_push_fLet
 :  forall ss fs t x
 ,  LiveS ss fs
 -> LiveS ss (fs :> FLet t x).
Proof.
 admit.
Qed.


Lemma liveS_pop_fLet
 :  forall ss fs t x
 ,  LiveS ss (fs :> FLet t x)
 -> LiveS ss fs.
Proof.
 admit.
Qed.


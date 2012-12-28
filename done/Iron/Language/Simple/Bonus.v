(* Bonus lemmas that aren't used by the main proofs *)

Require Import Iron.Language.Simple.Exp.
Require Import Iron.Language.Simple.Ty.
Require Import Iron.Language.Simple.SubstExpExp.


(********************************************************************)
(* Weakening type environments *)
Lemma type_tyenv_weaken1
 :  forall te x t1 t2
 ,  TYPE te          x t1
 -> TYPE (t2 <: te)  x t1.
Proof.
 intros. gen te t1.
 induction_type x.

 Case "XLam".
  eapply TYLam. rewrite snoc_cons. auto.
Qed.


Lemma type_tyenv_weaken
 :  forall tenv1 tenv2 x1 t1
 ,  TYPE tenv1            x1 t1
 -> TYPE (tenv2 >< tenv1) x1 t1.
Proof.
 intros. gen tenv1.
 induction tenv2; intros.
  rewrite app_nil_right. auto.
  rewrite app_snoc.  apply IHtenv2.
   apply type_tyenv_weaken1. auto.
Qed.


(********************************************************************)
(* Strengthen type environments *)
Lemma type_tyenv_strengthen
 :  forall te te' n x t
 ,   wfX te' x
 ->  te' = firstn n te
 ->  TYPE te  x t
 ->  TYPE te' x t.
Proof.
 intros. gen te te' n t.
 induction_type x; subst. 

 Case "XVar".
  destruct H; burn.

 Case "XLam".
  eapply TYLam.
  eapply IHx with (n := S n) (te := te :> t); burn.
Qed.


Lemma type_check_closed_in_empty_tyenv
 :  forall tenv x t
 ,  closedX x
 -> TYPE tenv x t
 -> TYPE nil  x t.
Proof.
 rip.
 eapply type_tyenv_strengthen; burn.
 symmetry.
 eapply firstn_zero.
Qed.


Theorem type_check_closed_in_any_tyenv
 :  forall tenv tenv' x1 t1
 ,  closedX x1
 -> TYPE tenv  x1 t1
 -> TYPE tenv' x1 t1.
Proof.
 rip.

 have (TYPE nil x1 t1) 
  by burn using type_check_closed_in_empty_tyenv.

 rrwrite (tenv' = tenv' >< nil).
 eauto using type_tyenv_weaken.
Qed.


(* If an expression is well formed under a given environment, 
   then all its indices are less than the length of this environment. 
   Lifting indices more than this length doesn't do anything *)
Theorem liftX_wfX
 :  forall d x e
 ,  d = length e
 -> wfX e x
 -> liftX d x = x.
Proof.
 intros. gen e d.
 induction x; intros; norm.
 
 Case "XVar".
  lift_cases; intros; eauto.
  false. subst. destruct H0.
   eapply get_above_false in H; auto. 

 Case "XLam".
  eapply IHx in H0; eauto.
  simpl in H0. symmetry. rewrite H. rewrite H0. auto.

 Case "XApp".
  spec IHx1 H1. rewrite IHx1; burn.
  spec IHx2 H2. rewrite IHx2; burn.
Qed.


(* If an expression is closed then it has no free indices. 
   Lifting it doesn't do anything. *)
Lemma liftX_closed
 :  forall x
 ,  closedX x
 -> liftX 0 x = x.
Proof.
 rip. eapply liftX_wfX; burn. burn.
Qed.


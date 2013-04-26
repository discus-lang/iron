
Require Import Iron.Language.SystemF2Data.Type.
Require Import Iron.Language.SystemF2Data.Exp.Relation.TypeX.
Require Import Iron.Language.SystemF2Data.Exp.Operator.SubstXX.


(* Substitute several expressions.

   Note that in the definition, each time we substitute an 
   exp (u), we need to lift it by the number of exps remaining
   in the list (us). This is because we're placing the substitued
   exp under the binders corresponding to the remaining ones.

   The added lifting is then gradually "undone" each time we
   substitue one of the remaining expressions. This happens due
   to the free variable/Gt case in the definition of substX.

   Example:
               (A->B), A |- 0 :: A
               (A->B), A |- 1 :: (A->B)
    (A->B), A, A, (A->B) |- (0 1) [1 0] :: B
   
    Substitute first exp in list.
            (A->B), A, A |- (2 0) [0] :: B

    We get '2' by adding the length of the remaining substitution
    (1) to the index substituted (1). The argument of the function 
    is changed from 1 to 0 by the free variable case of substX.

    Substitute remaining exp in list.
               (A->B), A |- (1 0) :: B

    Here, 0 is subst for 0, and 2 changes to 1 due as it's a free
    variable.
*)
Fixpoint substXXs (d: nat) (us: list exp) (xx: exp) :=
 match us with
 | nil      => xx
 | u :: us' => substXXs d us' 
                 (substXX d (liftXX (List.length us') 0 u)
                            xx)
 end.


(* Substitution of several expressions at once. *)
Theorem subst_exp_exp_list
 :  forall ds ks te x1 xs t1 ts
 ,  Forall2 (TYPE ds ks te)         xs ts
 -> TYPE ds ks (te >< ts) x1 t1
 -> TYPE ds ks te    (substXXs 0 xs x1) t1.
Proof.
 intros ds ks te x1 xs t1 ts HF HT.
 gen ts ks x1.
 induction xs; intros; inverts_type.

 - Case "base case".
   destruct ts. 
   + simpl. auto.
   + nope.

 - Case "step case".
   simpl. 
   destruct ts.
   + nope.
   + inverts HF.
     eapply IHxs. 
     * eauto.
     * simpl in HT.
       eapply subst_exp_exp. 
        eauto. 
        rrwrite (length xs = length ts).
        eapply type_tyenv_weaken_append. auto.
Qed.


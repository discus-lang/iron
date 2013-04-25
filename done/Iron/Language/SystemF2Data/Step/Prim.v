
Require Export Iron.Language.SystemF2Data.Exp.


(* Single step evaluation for primitives. *)
Fixpoint stepPrim (p : prim) (xs : list exp) : option exp :=
 match p, xs with
 |  PAdd,    XLit (LNat n1) :: XLit (LNat n2) :: nil 
 => Some (XLit (LNat (n1 + n2)))

 |  PIsZero, XLit (LNat n1) :: nil
 => Some (XLit (LBool (beq_nat n1 0)))

 | _, _
 => None
 end.


(* All primops return normal forms. *)
Lemma stepPrim_result_wnfX
 :  forall p xs v
 ,  stepPrim p xs = Some v
 -> wnfX v.
Proof.
 intros.
 destruct p.
 - Case "PAdd".
   simpl in H. 
    destruct xs; nope.
    destruct e;  nope.
    destruct l;  nope.
    destruct xs; nope.
    destruct e;  nope.
    destruct l;  nope.
    destruct xs; nope.
    inverts H. eauto.

 - Case "PIsZero".
   simpl in H.
    destruct xs; nope.
    destruct e;  nope.
    destruct l;  nope.
    destruct xs; nope.
    inverts H. eauto.
Qed.
Hint Resolve stepPrim_result_wnfX.


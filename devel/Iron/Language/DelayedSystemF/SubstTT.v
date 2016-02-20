
Require Export Iron.Language.DelayedSystemF.Ty.


(* Apply an type substitution to a type. *)
Fixpoint substTT (ss: @subst ty ki) (tt: ty) {struct tt} : ty  :=
 match tt with
 |  TCon c
 => tt

 |  TVar a
 => match lookupSubst a ss with
    | None                => tt
    | Some (BBind _ _ t)  => t
    end

 |  TForall ss2 a k t
 => TForall (ss >< mapExpOfSubst (substTT ss) ss2) a k t

 |  TFun t1 t2
 => TFun (substTT ss t1) (substTT ss t2)
 end.


Require Export Iron.Language.DelayedSystemF.Ty.


(* Apply an type substitution to a type. *)
Fixpoint substTT (st: @subst ty ki) (tt: ty) {struct tt} : ty  :=
 match tt with
 |  TCon c
 => tt

 |  TVar a
 => match lookupSubst a st with
    | None                => tt
    | Some (BBind _ _ t)  => t
    end

 |  TForall st2 a k t
 => TForall (st >< mapExpOfSubst (substTT st) st2) a k t

 |  TFun t1 t2
 => TFun (substTT st t1) (substTT st t2)
 end.


Definition substTE (st: @subst ty ki) (ee: @env ty): @env ty :=
 map (mapTypeOfSig (substTT st)) ee.
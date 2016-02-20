
Require Export Iron.Language.DelayedSystemF.Ty.
Require Export Iron.Language.DelayedSystemF.Exp.
Require Export Iron.Language.DelayedSystemF.SubstTT.


(* Apply a type and expression substitution to an expression. *)
Fixpoint substTX (st: @subst ty ki) (sx: @subst exp ty)
                 (xx: exp) {struct xx} : exp  :=
 match xx with
 | XVar n
 => match lookupSubst n sx with
    | None                => xx
    | Some (BBind _ _ x)  => x
    end

 |  XAbs ss n t x
 => XAbs (sx >< mapExpOfSubst (substTX st sx) ss) 
          n t x

 |  XApp x1 x2
 => XApp (substTX st sx x1) (substTX st sx x2)

 |  XABS  st2 sx2 a k x
 => XABS (st >< mapExpOfSubst (substTT st)    st2)
         (sx >< mapExpOfSubst (substTX st sx) sx2)
          a k x

 |  XAPP x1 t2 
 => XAPP (substTX st sx x1) t2
 end.

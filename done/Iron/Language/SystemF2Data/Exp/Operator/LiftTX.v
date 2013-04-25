
Require Export Iron.Language.SystemF2Data.Exp.Base.
Require Export Iron.Language.SystemF2Data.Exp.Alt.


(* Lift type indices in expressions. *)
Fixpoint liftTX (d: nat) (xx: exp) : exp :=
  match xx with
  |  XVar _     => xx

  |  XLAM x     
  => XLAM (liftTX (S d) x)

  |  XAPP x t 
  => XAPP (liftTX d x)  (liftTT 1 d t)
 
  |  XLam t x   
  => XLam (liftTT 1 d t)  (liftTX d x)

  |  XApp x1 x2
  => XApp (liftTX d x1) (liftTX d x2)

  |  XCon dc ts xs
  => XCon dc (map (liftTT 1 d) ts) (map (liftTX d) xs)

  |  XCase xx alts
  => XCase (liftTX d xx) (map (liftTA d) alts)

  |  XPrim p xs
  => XPrim p (map (liftTX d) xs)

  |  XLit l
  => XLit l
 end

 with liftTA (d: nat) (aa: alt) : alt :=
  match aa with
  |  AAlt dc xx
  => AAlt dc (liftTX d xx)
  end.


(* Data constructor of alternative is unchanged by lifting. *)
Lemma dcOfAlt_liftTA
 : forall d a
 , dcOfAlt (liftTA d a) = dcOfAlt a.
Proof.
 intros. destruct a. destruct d0. auto.
Qed.
Hint Rewrite dcOfAlt_liftTA : global.


(* Data constructor of alternatives are unchaged by lifting. *)
Lemma dcOfAlt_liftTA_map
 :  forall ix aa
 ,  map dcOfAlt (map (liftTA ix) aa)
 =  map dcOfAlt aa.
Proof.
 intros. induction aa; snorm; rewritess; eauto.
Qed.
Hint Rewrite dcOfAlt_liftTA_map : global.


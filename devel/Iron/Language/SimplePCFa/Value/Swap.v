
Require Export Iron.Language.SimplePCFa.Value.Exp.


(* Swap of adjacent indices at a given depth. *)
Fixpoint swapXV (d: nat) (vv: val) : val := 
  match vv with
  | VVar   d'    
  => if      beq_nat d'    d  then VVar (S d)
     else if beq_nat d' (S d) then VVar d
     else VVar d'
  | VConst c     => VConst c
  | VLam t x     => VLam t (swapXX (S d) x)
  | VFix t v     => VFix t (swapXV (S d) v)
  end

with    swapXX (d: nat) (xx: exp) : exp :=
  match xx with
  | XVal v       => XVal   (swapXV d v)
  | XLet t x1 x2 => XLet t (swapXX d x1) (swapXX (S d) x2)
  | XApp v1 v2   => XApp   (swapXV d v1) (swapXV d v2)
  | XOp1 o v     => XOp1 o (swapXV d v)
  | XIf v1 x2 x3 => XIf    (swapXV d v1) (swapXX d x2) (swapXX d x3)
  end.


Lemma swapXX_swapXX_id
 : forall d x
 , swapXX d (swapXX d x) = x.
Proof.
 intros. gen d.
 induction x using exp_mutind with
  (PV := fun v => forall d, swapXV d (swapXV d v) = v);
  intros; simpl;
   try (solve [snorm; burn; try omega]);
   try (solve [snorm; repeat rewritess; auto]).
Qed.
    

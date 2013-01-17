
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Lift.


Fixpoint liftTT_var (n : nat) (d : nat) (ix : nat)
 := if le_gt_dec d ix
     then ix + n
     else ix.


(* Mask effects on the given region, 
   replacing with the bottom effect. *)   (** TODO: let it take the region TCap as well *)
Fixpoint mask (r : nat) (e : ty) : ty
 := match e with
    |  TVar tc       => TVar tc
    |  TForall k t1  => TForall k (mask (liftTT_var 1 0 r) t1)
    |  TApp t1 t2    => TApp (mask r t1) (mask r t2)
    |  TSum t1 t2    => TSum (mask r t1) (mask r t2)
    |  TBot k        => TBot k

    |  TCon0 tc      => TCon0 tc

    |  TCon1 tc t1
    => match t1 with
       | TVar n' 
       => if beq_nat r n' 
             then TBot KEffect 
             else TCon1 tc (mask r t1)

       | _ =>     TCon1 tc (mask r t1)
       end
    
    | TCon2 tc t1 t2 => TCon2 tc (mask r t1) (mask r t2)

    | TCap  tc      => TCap tc
    end.
Arguments mask r e : simpl nomatch.


Lemma liftTT_mask
 :  forall r d t
 ,  mask r (liftTT 1 (r + d) t) = liftTT 1 (r + d) (mask r t).
Proof.
 intros. gen r d.
 induction t; intros; 
   try (solve [simpl; burn]);
   try (solve [simpl; f_equal; rewritess; auto]).

 Case "TVar".
  simpl. lift_cases. simpl. auto.
  simpl. auto.

  admit.


 Case "TCon1".
  admit. 
(*
 simpl.
  destruct t0.

  SCase "TVar".
   simpl.
    lift_cases.
     unfold mask.
      break (beq_nat r (n + 1)).
      break (beq_nat r n).
       simpl. auto.
       simpl. lift_cases. norm. 
 
      remember (beq_nat r (n0 + n)) as X. destruct X.
      remember (beq_nat r n0) as Y. destruct Y.
       simpl. auto.
       simpl. lift_cases.
     
    

     assert ( mask r (TCon1 TyConRead (TVar (n0 + n)))
            = if beq_nat r (n0 + n) then TBot KEffect else TCon1 TyConRead (TVar (n0 + n))).
     simpl.
     simpl.

     simpl match.

  SCase "TForall".
    simpl liftTT.
    set  (X0 := TForall k (liftTT n (S d) t0)).
     rrwrite (mask r (TCon1 t X0)          = TCon1 t (mask r X0)).
    subst X0.
    rrwrite (TForall k (liftTT n (S d) t0) = liftTT n d (TForall k t0)).
    rewritess. simpl. auto.

  SCase "TApp".
   simpl liftTT.
   set      (X0 := TApp (liftTT n d t0_1) (liftTT n d t0_2)).
    rrwrite (mask r (TCon1 t X0)           = TCon1 t (mask r X0)).
   subst X0.
   rrwrite  ( TApp (liftTT n d t0_1) (liftTT n d t0_2)
            = liftTT n d (TApp t0_1 t0_2)).
   rewritess. simpl. auto.
*)
Qed.


Lemma mask_liftTT_id
 : forall d t
 , mask d (liftTT 1 d t) = liftTT 1 d t.
Proof.
 intros. gen d. 
 induction t; intros;
  try (solve [simpl; burn]);
  try (solve [simpl; f_equal; norm; rewritess; auto]).

 Case "TVar".
  simpl. lift_cases; burn.

 Case "TCon1".
   admit.
Qed.


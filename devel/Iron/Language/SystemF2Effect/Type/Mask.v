
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Lift.


Fixpoint liftTT_var (n : nat) (d : nat) (ix : nat)
 := if le_gt_dec d ix
     then ix + n
     else ix.

(* Mask effects on the given region, 
   replacing with the bottom effect. *)
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

    | TCap  tc       => TCap tc
    end.
Arguments mask r e : simpl nomatch.


Lemma liftTT_mask
 :  forall r d t
 ,  mask r (liftTT 1 (1 + (r + d)) t) = liftTT 1 (1 + (r + d)) (mask r t).
Proof.
Opaque le_gt_dec.

 intros. gen r d.
 induction t; intros; 
   try (solve [simpl; burn]);
   try (solve [simpl; f_equal; rewritess; auto]).

 Case "TVar".
  simpl. lift_cases. simpl. auto.
  simpl. auto.

 Case "TForall".
  simpl. f_equal.
  rrwrite (S (r + d) = (r + 1) + d).
  rewrite IHt. auto.

 Case "TCon1".
  simpl.
  destruct t0.

  SCase "TVar".
   repeat (unfold mask; simpl; split_if; norm_beq_nat; auto; try omega).
          
  (* GAH. Most of this rubbish is just to force single step evaluation of mask.
     I can't work out how to do a 'simpl' with only a single step *)
  SCase "TForall".
   simpl liftTT.
   set     (X0 := TForall k (liftTT 1 (S (S (r + d))) t0)).
   rrwrite (mask r (TCon1 t X0)          = TCon1 t (mask r X0)).
   subst X0.
   rrwrite (TForall k (liftTT 1 (S (S (r + d))) t0) = liftTT 1 (S (r + d)) (TForall k t0)).
   rewritess. simpl. auto.
  
  SCase "TApp".
   simpl liftTT.
   set      (X0 := TApp (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)).
    rrwrite (mask r (TCon1 t X0)           = TCon1 t (mask r X0)).
   subst X0.
   rrwrite  ( TApp (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)
            = liftTT 1 (S (r + d)) (TApp t0_1 t0_2)).
   rewritess. simpl. auto.

  SCase "TSum".
   simpl liftTT.
   set      (X0 := TSum (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)).
    rrwrite (mask r (TCon1 t X0)           = TCon1 t (mask r X0)).
   subst X0.
   rrwrite  ( TSum (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)
            = liftTT 1 (S (r + d)) (TSum t0_1 t0_2)).
   rewritess. simpl. auto.

 SCase "TBot".
  burn.

 SCase "TCon0".
  burn.

 SCase "TCon1".
  simpl liftTT.
  set    (X0 := TCon1 t0 (liftTT 1 (S (r + d)) t1)).
   rrwrite (mask r (TCon1 t X0)           = TCon1 t (mask r X0)).
  subst X0.
  rrwrite  ( TCon1 t0 (liftTT 1 (S (r + d)) t1)
           = liftTT 1 (S (r + d)) (TCon1 t0 t1)).
  rewritess. auto.

  SCase "TCon2".
   simpl liftTT.
   set      (X0 := TCon2 t0 (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)).
    rrwrite (mask r (TCon1 t X0)           = TCon1 t (mask r X0)).
   subst X0.
   rrwrite  ( TCon2 t0 (liftTT 1 (S (r + d)) t0_1) (liftTT 1 (S (r + d)) t0_2)
            = liftTT 1 (S (r + d)) (TCon2 t0 t0_1 t0_2)).
   rewritess. simpl. auto.

 SCase "TCap".
  burn.
Qed.  


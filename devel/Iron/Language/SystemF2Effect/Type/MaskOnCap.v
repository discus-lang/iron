
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Lift.


(* Mask effects on the given region, 
   replacing with the bottom effect. *)
Fixpoint maskOnCap (r : nat) (e : ty) : ty
 := match e with
    |  TVar tc       => TVar tc
    |  TForall k t1  => TForall k (maskOnCap r t1)
    |  TApp t1 t2    => TApp (maskOnCap r t1) (maskOnCap r t2)
    |  TSum t1 t2    => TSum (maskOnCap r t1) (maskOnCap r t2)
    |  TBot k        => TBot k

    |  TCon0 tc      => TCon0 tc

    |  TCon1 tc t1
    => match t1 with
       | TCap (TyCapRegion n') 
       => if beq_nat r n' 
             then TBot KEffect 
             else TCon1 tc (maskOnCap r t1)

       | _ =>     TCon1 tc (maskOnCap r t1)
       end
    
    | TCon2 tc t1 t2 => TCon2 tc (maskOnCap r t1) (maskOnCap r t2)

    | TCap  tc       => TCap tc
    end.
Arguments maskOnCap r e : simpl nomatch.


Lemma liftTT_maskOnCAp
 :  forall r d t
 ,  maskOnCap r (liftTT 1 d t) = liftTT 1 d (maskOnCap r t).
Proof.
 intros. gen r d.
 induction t; intros; 
   try (solve [simpl; f_equal; burn]).

 Case "TVar".
  simpl. split_match. norm. norm.

 Case "TCon1".
  simpl. 
  destruct t0;
   try (solve [simpl in *; try rewritess; burn]).

   SCase "TVar".
    simpl. split_match. norm. norm.

   SCase "TCap". 
    simpl.
    destruct t0.
    unfold maskOnCap. 
    split_match. norm. norm.
Qed.
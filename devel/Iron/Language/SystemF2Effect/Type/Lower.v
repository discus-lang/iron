
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Wf.
Require Import Iron.Language.SystemF2Effect.Type.Lift.


(* Lowering of indices in types. *)
Fixpoint lowerTT (d: nat) (tt: ty) : option ty 
 := match tt with
    |  TVar ix
    => match nat_compare ix d with
       | Eq                  => None
       | Gt                  => Some (TVar (ix - 1))
       | _                   => Some (TVar  ix)
       end

    |  TForall k t 
    => match lowerTT (S d) t with
        | Some t2            => Some (TForall k t2)
        | _                  => None
       end

  
    |  TApp t1 t2
    => match lowerTT d t1, lowerTT d t2 with
        | Some t1', Some t2' => Some (TApp t1' t2')
        | _, _               => None
       end

    |  TSum t1 t2
    => match lowerTT d t1, lowerTT d t2 with
        | Some t1', Some t2' => Some (TSum t1' t2')
        | _, _               => None
       end

    |  TBot k                => Some (TBot k)

    |  TCon0 tc              => Some (TCon0 tc)

    |  TCon1 tc t1
    => match lowerTT d t1 with
       | Some t1'            => Some (TCon1 tc t1')
       | _                   => None
       end

    |  TCon2 tc t1 t2
    => match lowerTT d t1, lowerTT d t2 with
       | Some t1', Some t2'  => Some (TCon2 tc t1' t2')
       | _, _                => None
       end

    |  TCap _                => Some tt
    end.


Lemma lowerTT_liftTT_some
 : forall t d d'
 , lowerTT d (liftTT 1 (1 + d + d') (liftTT 1 d t)) 
 = Some (liftTT 1 (d + d') t).
Proof.
 intros. gen d.
 induction t; intros;
  try burn;
  try (solve [ simpl; split_match
             ; repeat (rewritess; norm; auto)]).

(* Keep this opaque so simpl doesn't unfold it *)
Opaque le_gt_dec.
 Case "TVar".
  simpl in *.
  lift_cases; simpl;
  lift_cases; simpl; 
  lift_cases; repeat (simpl; nnat); burn; try omega.
Transparent le_gt_dec.  
Qed.


Lemma lowerTT_some_liftTT
 :  forall d t1 t2 
 ,  lowerTT   d t1 = Some t2
 -> liftTT  1 d t2 = t1.
Proof.
 intros. gen d t2.
 induction t1; intros;
  try burn;
  try (solve [ norm; split_match
             ; burn; try nope
             ; repeat norm; f_equal; repeat norm; nope]).

 Case "TVar".
  simpl in *.
  split_match; burn.
   norm. simpl. lift_cases; burn; omega.
   norm. simpl. lift_cases; burn.
    destruct n; burn. omega.
Qed.
Hint Resolve lowerTT_some_liftTT.
Hint Rewrite lowerTT_some_liftTT.


Lemma lowerTT_liftTT_succ
 : forall d t1 t2
 ,  lowerTT 0 t1                    = Some t2
 -> lowerTT 0 (liftTT 1 (1 + d) t1) = Some (liftTT 1 d t2).
Proof.
 intros.
 eapply lowerTT_some_liftTT in H.
 symmetry in H. subst.
 eapply lowerTT_liftTT_some.
Qed.
Hint Resolve lowerTT_liftTT_succ.
Hint Rewrite lowerTT_liftTT_succ.


Lemma lowerTT_liftTT
 : forall d t
 , lowerTT d (liftTT 1 d t) = Some t.
Proof.
 intros. gen d.
 lift_burn t.

 Case "TVar".
  simpl; lift_cases; simpl; lift_cases; try omega; repeat norm.
Qed.
Hint Resolve lowerTT_liftTT.
Hint Rewrite lowerTT_liftTT.


Lemma lowerTT_liftTT_switch
 : forall d t
 , lowerTT d (liftTT 1 (S d) (liftTT 1 d t)) 
 = Some (liftTT 1 d t).
Proof.
 intros. gen d.
 lift_burn t.

 Case "TVar".
  simpl; 
   lift_cases; unfold liftTT;
   lift_cases; simpl; lift_cases; burn; omega.
Qed.  
Hint Resolve lowerTT_liftTT_switch.
Hint Rewrite lowerTT_liftTT_switch.


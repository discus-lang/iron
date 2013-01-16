
Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Wf.
Require Import Iron.Language.SystemF2Effect.Type.Lift.


(* Lowering of indices in types. *)
Fixpoint lowerTT (d: nat) (tt: ty) : option ty 
 := match tt with
    |  TCon _      => Some tt
    |  TCap _      => Some tt

    |  TVar ix
    => match nat_compare ix d with
       | Eq => None
       | Gt => Some (TVar (ix - 1))
       | _  => Some (TVar  ix)
       end

    |  TForall k t 
    => match lowerTT (S d) t with
        | Some t2 => Some (TForall k t2)
        | _       => None
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
    end.


(* Cleanup the Coqage here. 
   How to we match on an 'if' scrutinee to remove the need for explicit
   remembers?
*)
Lemma lowerTT_liftTT_some
 : forall t d d'
 , lowerTT d (liftTT 1 (1 + d + d') (liftTT 1 d t)) 
 = Some (liftTT 1 (d + d') t).
Proof.
(* Keep this opaque so simpl doesn't unfold it *)
Opaque le_gt_dec.
 intros. gen d.
 induction t; intros; burn.

 Case "TVar".
  simpl in *.
  lift_cases; simpl;
  lift_cases; simpl; 
  lift_cases; repeat (simpl; nnat); burn; try omega.

 Case "TForall".
  simpl.
  remember (lowerTT (S d) (liftTT 1 (S (S (d + d'))) (liftTT 1 (S d) t))) as X.
  destruct X;
  erewrite IHt in HeqX;
   inverts HeqX; trivial.

 Case "TApp".
  simpl.
  remember (lowerTT d (liftTT 1 (S (d + d')) (liftTT 1 d t1))) as X.
  destruct X;
  erewrite IHt1 in HeqX.

  remember (lowerTT d (liftTT 1 (S (d + d')) (liftTT 1 d t2))) as Y;
  destruct Y.
  erewrite IHt2 in HeqY; 
   inverts HeqX; inverts HeqY; trivial.

  inverts HeqX.
  erewrite IHt2 in HeqY; nope.

  nope.

 Case "TSum".
  simpl.
  remember (lowerTT d (liftTT 1 (S (d + d')) (liftTT 1 d t1))) as X.
  destruct X;
  erewrite IHt1 in HeqX.

  remember (lowerTT d (liftTT 1 (S (d + d')) (liftTT 1 d t2))) as Y;
  destruct Y.
  erewrite IHt2 in HeqY; 
   inverts HeqX; inverts HeqY; trivial.

  inverts HeqX.
  erewrite IHt2 in HeqY; nope.

  nope.
Transparent le_gt_dec.  
Qed. 


Lemma lowerTT_some_liftTT
 :  forall d t1 t2 
 ,  lowerTT   d t1 = Some t2
 -> liftTT  1 d t2 = t1.
Proof.
 intros. gen d t2.
 induction t1; intros;
  try solve [inverts H; burn].

 Case "TVar".
  simpl in *.
  remember (nat_compare n d) as X.
  destruct X; burn.
  symmetry in HeqX. apply nat_compare_lt in HeqX.
  inverts H. simpl. lift_cases; burn; omega.

  symmetry in HeqX. apply nat_compare_gt in HeqX.
  inverts H. simpl. lift_cases; burn.
   destruct n; burn.
   omega.

 Case "TForall".
  simpl in *.
  remember (lowerTT (S d) t1) as X.
  destruct X.
   inverts H.
   simpl. f_equal. eauto.
   false.

 Case "TApp".
  simpl in *.
  remember (lowerTT d t1_1) as X. destruct X; nope.
  remember (lowerTT d t1_2) as X. destruct X; nope.
  inverts H; burn. 
   simpl.
   rewrite IHt1_1; burn.
   rewrite IHt1_2; burn.

 Case "TSum".
  simpl in *.
  remember (lowerTT d t1_1) as X. destruct X; nope.
  remember (lowerTT d t1_2) as X. destruct X; nope.
  inverts H; burn.
   simpl.
   rewrite IHt1_1; burn.
   rewrite IHt1_2; burn.
Qed.
Hint Resolve lowerTT_some_liftTT.
Hint Rewrite lowerTT_some_liftTT.


Lemma lowerTT_liftTT
 : forall d t
 , lowerTT d (liftTT 1 d t) = Some t.
Proof.
 intros. gen d.
 lift_burn t.

 Case "TVar".
  simpl. lift_cases; simpl.
  lift_cases; try omega.
   repeat norm.

  lift_cases; try omega. auto.
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
  simpl. 
  lift_cases;
   unfold liftTT;
   lift_cases;
    simpl; lift_cases; burn; omega.
Qed.  
Hint Resolve lowerTT_liftTT_switch.
Hint Rewrite lowerTT_liftTT_switch.




Require Import Iron.Language.SystemF2Effect.Type.Ty.
Require Import Iron.Language.SystemF2Effect.Type.Wf.
Require Import Iron.Language.SystemF2Effect.Type.LiftTT.


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


Ltac burn_lowerTT t := 
  induction t;
  first [ solve [snorm; f_equal; try omega]
        | solve [repeat (snorm; f_equal; eauto; rewritess; nope) ]].


Lemma lowerTT_liftTT_some
 : forall t d d'
 , lowerTT d (liftTT 1 (1 + d + d') (liftTT 1 d t)) 
 = Some (liftTT 1 (d + d') t).
Proof.
 intros. gen d. burn_lowerTT t.
Qed.
Hint Resolve lowerTT_liftTT_some.
Hint Rewrite lowerTT_liftTT_some : global.


Lemma lowerTT_some_liftTT
 :  forall d t1 t2 
 ,  lowerTT   d t1 = Some t2
 -> liftTT  1 d t2 = t1.
Proof.
 intros. gen d t2. burn_lowerTT t1.
Qed.
Hint Resolve lowerTT_some_liftTT.
Hint Rewrite lowerTT_some_liftTT : global.


Lemma lowerTT_liftTT_succ
 : forall d t1 t2
 ,  lowerTT 0 t1                    = Some t2
 -> lowerTT 0 (liftTT 1 (1 + d) t1) = Some (liftTT 1 d t2).
Proof.
 intros.
 eapply lowerTT_some_liftTT in H. subst.
 eapply lowerTT_liftTT_some.
Qed.
Hint Resolve lowerTT_liftTT_succ.
Hint Rewrite lowerTT_liftTT_succ : global.


Lemma lowerTT_liftTT
 : forall d t
 , lowerTT d (liftTT 1 d t) = Some t.
Proof.
 intros. gen d. burn_lowerTT t.
Qed.
Hint Resolve lowerTT_liftTT.
Hint Rewrite lowerTT_liftTT : global.


Lemma lowerTT_liftTT_switch
 : forall d t
 , lowerTT d (liftTT 1 (S d) (liftTT 1 d t)) 
 = Some (liftTT 1 d t).
Proof.
 intros. gen d. burn_lowerTT t.
Qed.  
Hint Resolve lowerTT_liftTT_switch.
Hint Rewrite lowerTT_liftTT_switch : global.


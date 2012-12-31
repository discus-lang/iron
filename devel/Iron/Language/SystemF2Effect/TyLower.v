
Require Import Iron.Language.SystemF2Effect.TyExp.
Require Import Iron.Language.SystemF2Effect.TyWfT.


(* Lowering of indices in types. *)
Fixpoint lowerTT (d: nat) (tt: ty) : option ty 
 := match tt with
    | TVar ix
    => match nat_compare ix d with
       | Eq => None
       | Gt => Some (TVar (ix - 1))
       | _  => Some (TVar  ix)
       end

    |  TCon _      => Some tt

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

   


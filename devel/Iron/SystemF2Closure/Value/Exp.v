
Require Export Iron.SystemF2Closure.Type.


(******************************************************************************)
(* Constants *)
Inductive const : Type := 
  | CUnit   : const
  | CNat    : nat   -> const
  | CBool   : bool  -> const.
Hint Constructors const.


Fixpoint typeOfConst (c : const) : ty := 
  match c with
  | CUnit     => TUnit
  | CNat  _   => TNat
  | CBool _   => TBool
  end.


(* Primitive Operators *)
Inductive op1 : Type := 
  | OSucc   : op1
  | OIsZero : op1.
Hint Constructors op1.


(* Values *)
Inductive val : Type := 
  | VVar    : nat   -> val
  | VLoc    : nat   -> val
  | VLam    : ty    -> exp -> val
  | VLAM    : ki    -> exp -> val
  | VConst  : const -> val

(* Expressions *)
with     exp : Type :=
  | XVal    : val -> exp

  (* Lift a literal to a pure computation. *)
  | XClose  : val -> exp    (* Construct a computation type. *)
  | XOpen   : val -> exp    (* Open   up a computation type. *)

  (* Sequence evaluation. *)
  | XLet    : ty  -> exp -> exp -> exp

  (* Function application. *)
  | XApp    : val -> val -> exp

  (* Type application. *)
  | XAPP    : val -> ty  -> exp

  (* Pure operators *)
  | XOp1    : op1 -> val -> exp

  (* Store operators *)
  | XNew    : exp -> exp
  | XAlloc  : ty  -> val -> exp
  | XRead   : ty  -> val -> exp
  | XWrite  : ty  -> val -> val -> exp.

Hint Constructors val.
Hint Constructors exp.


(******************************************************************************)
(* Induction principle for expressions. *)
Lemma exp_mutind : forall 
    (PX : exp -> Prop)
    (PV : val -> Prop)
 ,  (forall n,                                     PV (VVar   n))
 -> (forall l,                                     PV (VLoc   l))
 -> (forall t x,        PX x                    -> PV (VLam   t x))
 -> (forall k x,        PX x                    -> PV (VLAM   k x))
 -> (forall c,                                     PV (VConst c))
 -> (forall v,          PV v                    -> PX (XVal   v))
 -> (forall v,          PV v                    -> PX (XClose v))
 -> (forall v,          PV v                    -> PX (XOpen v))
 -> (forall t x1 x2,    PX x1 -> PX x2          -> PX (XLet   t x1 x2))
 -> (forall v1 v2,      PV v1 -> PV v2          -> PX (XApp   v1 v2))
 -> (forall v t,        PV v                    -> PX (XAPP   v  t))
 -> (forall o v,        PV v                    -> PX (XOp1 o v))
 -> (forall x,          PX x                    -> PX (XNew   x))
 -> (forall r v,        PV v                    -> PX (XAlloc r v))
 -> (forall r v,        PV v                    -> PX (XRead  r v))
 -> (forall r v1 v2,    PV v1 -> PV v2          -> PX (XWrite r v1 v2))
 ->  forall x, PX x.
Proof. 
 intros PX PV.
 intros hVar hLoc hLam hLAM hConst 
        hVal 
        hClose hOpen
        hLet  hApp   hAPP   hOp1
        hNew  hAlloc hRead  hWrite.
 refine (fix  IHX x : PX x := _
         with IHV v : PV v := _
         for  IHX).

 (* expressions *)
 case x; intros.
 apply hVal.   apply IHV.
 apply hClose. apply IHV.
 apply hOpen.  apply IHV.
 apply hLet.   apply IHX. apply IHX.
 apply hApp.   apply IHV. apply IHV.
 apply hAPP.   apply IHV.
 apply hOp1.   apply IHV.
 apply hNew.   apply IHX.
 apply hAlloc. apply IHV.
 apply hRead.  apply IHV.
 apply hWrite. apply IHV. apply IHV.

 (* values *)
 case v; intros.
 apply hVar.
 apply hLoc.
 apply hLam. apply IHX.
 apply hLAM. apply IHX.
 apply hConst.
Qed.


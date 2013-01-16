
Require Export Iron.Language.SystemF2Effect.Kind.


(* Type Constructors. *)
Inductive tycon : Type :=

  (* Value type constructors *)
  | TyConFun    : tycon
  | TyConUnit   : tycon
  | TyConBool   : tycon
  | TyConNat    : tycon
  | TyConRef    : tycon

  (* Effect type constructors *)
  | TyConRead   : tycon
  | TyConWrite  : tycon
  | TyConAlloc  : tycon.
Hint Constructors tycon.


Fixpoint kindOfTyCon (tc : tycon) :=
  match tc with
  | TyConFun      => KFun KData (KFun KEffect (KFun KData KData))
  | TyConUnit     => KData
  | TyConBool     => KData
  | TyConNat      => KData
  | TyConRef      => KFun KRegion (KFun KData KData)
    
  | TyConRead     => KFun KRegion KEffect
  | TyConWrite    => KFun KRegion KEffect
  | TyConAlloc    => KFun KRegion KEffect
  end.


Fixpoint tycon_beq t1 t2 :=
  match t1, t2 with
  | TyConFun,       TyConFun       => true
  | TyConUnit,      TyConUnit      => true
  | TyConBool,      TyConBool      => true
  | TyConNat,       TyConNat       => true
  | TyConRef,       TyConRef       => true

  | TyConRead,      TyConRead      => true
  | TyConWrite,     TyConWrite     => true
  | TyConAlloc,     TyConAlloc     => true
  | _,              _              => false
  end.


Definition isTyConFun  (tc: tycon) : Prop :=
  match tc with
  | TyConFun      => True
  | _             => False
  end.
Hint Unfold isTyConFun.


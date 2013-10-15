
(* Type constructors are split into several groups depending on how
   many arguments need to be applied for the overall type to be 
   well formed. We keep primitive types like Read, Write and Ref fully
   applied to make the mechanisation easier. In the full language the
   ability to partially apply these could be recovered using 
   type synonyms. *)
Require Export Iron.Language.SystemF2Effect.Kind.


(********************************************************************)
(* Type Constructors. *)
Inductive tycon0 : Type :=
 | TyConFun    : tycon0
 | TyConUnit   : tycon0
 | TyConBool   : tycon0
 | TyConNat    : tycon0.
Hint Constructors tycon0.


Fixpoint kindOfTyCon0 (tc : tycon0) :=
 match tc with
 | TyConFun     => KFun KData (KFun KEffect (KFun KData KData))
 | TyConUnit    => KData
 | TyConBool    => KData
 | TyConNat     => KData
 end.


Fixpoint tycon0_beq tc1 tc2 :=
 match tc1, tc2 with
 | TyConFun,    TyConFun    => true
 | TyConUnit,   TyConUnit   => true
 | TyConBool,   TyConBool   => true
 | TyConNat,    TyConNat    => true
 | _,           _           => false
 end.


(********************************************************************)
(* Type constructors with at least one applied argument. *)
Inductive tycon1 : Type :=
 | TyConRead   : tycon1
 | TyConWrite  : tycon1
 | TyConAlloc  : tycon1.


Fixpoint kindOfTyCon1 (tc : tycon1) :=
 match tc with   
 | TyConRead    => KFun KRegion KEffect
 | TyConWrite   => KFun KRegion KEffect
 | TyConAlloc   => KFun KRegion KEffect
 end.


Fixpoint tycon1_beq tc1 tc2 :=
 match tc1, tc2 with
 | TyConRead,   TyConRead   => true
 | TyConWrite,  TyConWrite  => true
 | TyConAlloc,  TyConAlloc  => true
 | _,           _           => false
 end.


Definition isEffectTyCon_b (tc : tycon1) :=
 match tc with
 | TyConRead     => true
 | TyConWrite    => true
 | TyConAlloc    => true
 end.


(********************************************************************)
(* Type constructors with at least two applied arguments. *)
Inductive tycon2 : Type :=
 | TyConRef    : tycon2.
Hint Constructors tycon2.


Fixpoint kindOfTyCon2 (tc : tycon2) :=
 match tc with
 | TyConRef      => KFun KRegion (KFun KData KData)
 end.


Fixpoint tycon2_beq tc1 tc2 :=
 match tc1, tc2 with
 | TyConRef,     TyConRef  => true
 end.



Require Export Iron.Language.SystemF2Data.Type.Exp.
Require Export Iron.Language.SystemF2Data.Type.Relation.KindT.
Require Export Iron.Language.SystemF2Data.Type.Def.DaCon.


(********************************************************************)
(* Definitions. 
   Carries meta information about type and data constructors. *)
Inductive def  : Type :=
 (* Definition of a data type constructor *)
 | DefDataType 
   :  tycon        (* Name of data type constructor *)
   -> list ki      (* Kinds of type parameters *)
   -> list datacon (* Data constructors that belong to this type *)
   -> def

 (* Definition of a data constructor *)
 | DefData 
   :  datacon      (* Name of data constructor *)
   -> list ty      (* Types of arguments *)
   -> tycon        (* Type constructor of constructed data *)
   -> def.
Hint Constructors def.


(* Definition environment.
   Holds the definitions of all current type and data constructors. *)
Definition defs  := list def.


(* Lookup the def of a given type constructor.
   Returns None if it's not in the list. *)
Fixpoint getTypeDef (tc: tycon) (ds: defs) : option def := 
 match ds with 
 | ds' :> DefDataType tc' _ _ as d
 => if tycon_beq tc tc' 
     then  Some d
     else  getTypeDef tc ds'

 | ds' :> _ => getTypeDef tc ds'
 | Empty    => None
 end.


Lemma getTypeDef_in
 :  forall tc ds ddef
 ,  getTypeDef tc ds = Some ddef
 -> In ddef ds.
Proof.
 intros.
 induction ds.
 - false.
 - destruct a; burn.
Qed.
Hint Resolve getTypeDef_in.


(* Lookup the def of a given data constructor. 
   Returns None if it's not in the list. *)
Fixpoint getDataDef (dc: datacon) (ds: defs) : option def := 
 match ds with 
 | ds' :> DefData dc' _ _ as d
 => if datacon_beq dc dc' 
     then  Some d
     else  getDataDef dc ds'

 | ds' :> _ => getDataDef dc ds'
 | Empty    => None
 end.


Lemma getDataDef_in
 :  forall tc ds ddef
 ,  getDataDef tc ds = Some ddef
 -> In ddef ds.
Proof.
 intros.
 induction ds.
 - false.
 - destruct a; burn.
Qed.
Hint Resolve getDataDef_in.




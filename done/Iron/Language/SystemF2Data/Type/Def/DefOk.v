
Require Export Iron.Language.SystemF2Data.Type.Def.Def.


(********************************************************************)
(* Check that a definition is ok. *)
Inductive DEFOK : list def -> def -> Prop :=
 (* Check that a data type definition is ok *)
 | DefOkType
   :  forall ds tc ks dcs
      (* Type constructor must be an algebraic data type constructor, 
         not the function type constructor or a primitive type. *)
   ,  isTyConData tc

      (* There must be at least one data constructor *)
   -> length dcs > 0
      
      (* All the data constructors must be present in the list of defs *)
   -> Forall (fun dc => exists ddef, getDataDef dc ds = Some ddef) dcs

   -> DEFOK ds (DefDataType tc ks dcs)

 (* Check that a data constructor definition is ok. *)
 | DefOkData
   :  forall tc ds ks dcs tsArgs tag arity
      (* Type constructor must be an algebraic data type constructor, 
         not the function type constructor or a primitive type. *)
   ,  isTyConData tc

      (* Get the data type def this data ctor belongs to *)
   -> getTypeDef tc ds = Some (DefDataType tc ks dcs)

      (* Data ctor must be one of the ctors in the data type def *)
   -> In (DataCon tag arity) dcs

   -> length tsArgs = arity

      (* All the ctor arg types must be well kinded in an environment
         consisting of just the parameter types. *)
   -> Forall (fun t => KIND ks t KStar) tsArgs

   -> DEFOK ds (DefData (DataCon tag arity) tsArgs tc).


(* Check that some data type definitions and their
   associated constructors are ok *)
Definition DEFSOK (ds: list def) : Prop :=
  Forall (DEFOK ds) ds.



(********************************************************************)
Lemma getTypeDef_ok 
 :  forall ds tc ddef
 ,  DEFSOK ds
 -> getTypeDef tc ds = Some ddef
 -> DEFOK  ds ddef.
Proof.
 intros.
 unfold DEFSOK in H.
 apply getTypeDef_in in H0.
 snorm. 
Qed.  
Hint Resolve getTypeDef_ok.


Lemma getDataDef_ok
 :  forall ds tc ddef
 ,  DEFSOK ds
 -> getDataDef tc ds = Some ddef
 -> DEFOK ds ddef.
Proof.
 intros.
 unfold DEFSOK in H.
 apply getDataDef_in in H0.
 snorm.
Qed.
Hint Resolve getDataDef_ok.


Lemma getDataDef_datacon_in
 :  forall d ds ts tc ks dcs
 ,  DEFSOK ds
 -> getDataDef d  ds = Some (DefData     d  ts tc)
 -> getTypeDef tc ds = Some (DefDataType tc ks dcs)
 -> In d dcs.
Proof.
 intros.
 have (DEFOK ds (DefData d ts tc))       as HD; inverts HD.
 have (DEFOK ds (DefDataType tc ks dcs)) as HT; inverts HT.
 rewrite H1 in H6. inverts H6.
 auto.
Qed.
Hint Resolve getDataDef_datacon_in.


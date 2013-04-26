
Require Export Iron.Language.SystemF2Data.Type.Def.DaCon.
Require Export Iron.Language.SystemF2Data.Type.Def.Def.
Require Export Iron.Language.SystemF2Data.Type.Def.DefOk.


(* Tactic to help unpack data definitions *)
Ltac ddef_merge
 := match goal with 
    | [ H1 : getTypeDef ?tc ?ds = Some (DefDataType _ ?ks0 ?dcs0)
      , H2 : getTypeDef ?tc ?ts = Some (DefDataType _ ?ks1 ?dcs1) |- _ ]
    => assert (ks1 = ks0 /\ dcs1 = dcs0) as HA
         by (rewrite H1 in H2; inverts H2; auto);
       inverts HA; clear H2

    | [ H1 : getDataDef ?dc ?ds = Some (DefData _ ?dc0 ?ts0)
      , H2 : getDataDef ?dc ?ts = Some (DefData _ ?dc1 ?ts1) |- _ ]
    => assert (dc1 = dc0 /\ ts1 = ts0) as HA
         by (rewrite H1 in H2; inverts H2; auto);
       inverts HA; clear H2
    end.


Tactic Notation "defok" constr(ds) constr(ddef)
 := let H := fresh
    in assert (DEFOK ds ddef) as H by burn;
       inverts H; try ddef_merge.

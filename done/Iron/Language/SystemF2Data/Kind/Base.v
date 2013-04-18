
Require Export Iron.Language.SystemF2Data.Base.


(* Kinds *)
Inductive ki : Type :=
 | KStar   : ki
 | KFun    : ki -> ki -> ki.
Hint Constructors ki.


(* Kind Environments *)
Definition kienv := list ki.
Hint Unfold kienv.



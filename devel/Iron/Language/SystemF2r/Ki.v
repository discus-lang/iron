
Require Export Iron.Language.SystemF2r.Base.


(* Kinds *)
Inductive ki : Type :=
 | KData   : ki
 | KFun    : ki -> ki -> ki.
Hint Constructors ki.


(* Kind Environments *)
Definition kienv := list ki.


(* Kind env is the same as another, but with a new element. *)
Definition keK      (k : ki)  (ke : kienv) (ke' : kienv) : Prop
 := ke :> k  = ke'.


(* Kind env is the same as another, but with a new element. *)
Definition keKi     (i : nat) (k : ki)  (ke : kienv) (ke' : kienv) : Prop
 := insert i k ke = ke'.


(* Kind is the ith element of a kind environemnt. *)
Definition keAtK    (i : nat) (ke : kienv) (k   : ki) : Prop
 := get i ke = Some k.


(* Get the size of a kind environment. *)
Definition keSize (ke : kienv) : nat
 := length ke.




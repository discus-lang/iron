
Require Export Iron.Language.SystemF2Cap.Base.


(* Kinds *)
Inductive ki : Type :=
 (* Kind of data values. *)
 | KData   : ki              

 (* Kind of region variables and region handles. *)
 | KRegion : ki              

 (* Kind of effect types. *)
 | KEffect : ki

 (* Kind of type constructors. *)
 | KFun    : ki -> ki -> ki.

Hint Constructors ki.


(* Roles describe how each binding was added to the kind environent. *)
Inductive role : Type :=
 (* Type is bound abstractly.
    Used for type abstractions like with (/\(a : k). x)  *)
 | OAbs 

 (* Type is bound concretely.
    Used for private and extension regions, like with (private r with caps in x) 
    In the expression 'x', the type 'r' refers to a concrete region with
    specific capabilities. *)
 | OCon.


(* Kind Environments *)
Definition kienv := list (role * ki).
Hint Unfold kienv.

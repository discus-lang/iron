
Require Import Iron.Language.SystemF2Data.Exp.
Require Export Iron.Data.Context.
Require Export Iron.Data.Chain.


(*  Evaluation contexts for expressions.
    This describes a place in the exp AST where the sub-expression
    there is able to take an evaluation step *)
Inductive exp_ctx : (exp -> exp) -> Prop :=

 (* Left of an application *)
 | XcApp1
   :  forall x2
   ,  exp_ctx  (fun xx => XApp xx x2)

 (* The right of an application can step only when the left is
    already a value. *)
 | XcApp2 
   :  forall v1
   ,  value v1
   -> exp_ctx  (fun xx => XApp v1 xx)

 | XcAPP
   :  forall t2
   ,  exp_ctx  (fun xx => XAPP xx t2)

 | XcCon 
   :  forall dc ts C
   ,  exps_ctx wnfX C 
   -> exp_ctx  (fun xx => XCon dc ts (C xx))

 (* As the XPrim constructor contains a list of sub-expressions, 
    we need an additional exps_ctx context to indicate which one 
    we're talking about. *)
 | XcPrim
   :  forall p C
   ,  exps_ctx wnfX C
   -> exp_ctx  (fun xx => XPrim p (C xx))

 (* We need to reduce the discriminant of a case to a value. *)
 | XcCase
   :  forall alts
   ,  exp_ctx  (fun xx => XCase xx alts).

Hint Constructors exp_ctx. 


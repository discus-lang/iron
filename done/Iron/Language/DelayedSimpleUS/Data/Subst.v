
Require Export Coq.Strings.String.
Require Export Iron.Language.DelayedSimpleUS.Tactics.Chargueraud.
Require Export Iron.Language.DelayedSimpleUS.Data.Lists.


(********************************************************************)
(* Variables want to be named. *)
Definition name := string.


(********************************************************************)
(* Bindings. *)
Inductive bind {A: Type}: Type :=
 | Bind   : name -> A -> @bind A.
Hint Constructors bind.


(* Get the name of a binding. *)
Definition nameOfBind {X}
  (b: @bind X): name :=
 match b with
 | Bind n _ => n
 end.


(* Get the expression of a binding. *)
Definition expOfBind {X}
  (b: @bind X): X :=
 match b with
 | Bind _ x => x
 end.


(* Apply a function to the expression component of a binding. *)
Definition mapExpOfBind {X} 
  (f: X -> X) (b: @bind X): @bind X :=
 match b with
 | Bind n x => Bind n (f x)
 end.


(********************************************************************)
(* An environment is a list of bindings. *)
Definition env (A: Type) 
 := list (@bind A).


(* Lookup expression bound to the given variable in an environment. *)
Fixpoint lookupEnv {A: Type} (var: string) (ee: env A) : option A :=
 match ee with
 |  nil                
 => None

 |  Bind v x :: rest
 => match string_dec var v with
    | left  _ => Some x
    | right _ => lookupEnv var rest
    end
 end.


Lemma lookupEnv_some_app
 :  forall {A} env1 env2 n x
 ,  @lookupEnv A n (env1 ++ env2) = Some x
 -> @lookupEnv A n env1 = Some x
 \/ @lookupEnv A n env2 = Some x.
Proof.
 intros. gen x.
 induction env1; intros.
 - simpl in *. firstorder.
 - simpl in *.
   destruct a.
   remember (string_dec n n0) as b.
   destruct b.
   + firstorder.
   + firstorder.
Qed.


Lemma lookupEnv_app_infront
 :  forall A n env1 env2 x1 x2
 ,  @lookupEnv A n  env1          = Some x2
 -> @lookupEnv A n (env1 ++ env2) = Some x1
 -> x1 = x2.
Proof.
 intros A n env1 env2 x1 x2 HL1 HL2.
 induction env1.
 - simpl in *. congruence.
 - simpl in *. destruct a.
   remember (string_dec n n0) as X.
   destruct X.
   + inverts HL1. congruence.
   + firstorder. 
Qed.


Lemma lookupEnv_app_inback
 :  forall A n env1 env2 x1
 ,  @lookupEnv A n  env1          = None
 -> @lookupEnv A n (env1 ++ env2) = Some x1
 -> @lookupEnv A n  env2          = Some x1.
Proof.
 intros A n env1 env2 x1 HL1 HL12.
 induction env1.
 - simpl in *. assumption.
 - simpl in *. destruct a.
   remember (string_dec n n0) as X.
   destruct X.
   + congruence.
   + firstorder.
Qed.


(********************************************************************)
Inductive EnvZip {A B} : env A -> env B -> env (A * B) -> Prop :=
 | EnvZipNil 
   : EnvZip nil nil nil

 | EnvZipCons
   :  forall n a (aa : env A) b (bb : env B) ab
   ,  EnvZip aa bb ab
   -> EnvZip (Bind n a :: aa) (Bind n b :: bb) (Bind n (a, b) :: ab).
Hint Constructors EnvZip.


Lemma EnvZip_some_1of2
 :  forall {A B} e1 e2 e12 n x2
 ,  EnvZip e1 e2 e12
 -> @lookupEnv A n e2 = Some x2
 -> exists x1, 
    @lookupEnv B n e1 = Some x1.
Proof.
 intros.
 induction H.
 - simpl in H0.
   congruence.
 - simpl in *.
   remember (string_dec n n0) as X.
   destruct X.
   + subst.
     inverts H0.
     exists a. trivial.
   + specializes IHEnvZip H0.
     trivial.
Qed.


Lemma EnvZip_some_2of1
 :  forall {A B} e1 e2 e12 n x1
 ,  EnvZip e1 e2 e12
 -> @lookupEnv A n e1 = Some x1
 -> exists x2, 
    @lookupEnv B n e2 = Some x2.
Proof.
 intros.
 induction H.
 - simpl in H0.
   congruence.
 - simpl in *.
   remember (string_dec n n0) as X.
   destruct X.
   + subst.
     inverts H0.
     exists b. trivial.
   + specializes IHEnvZip H0.
     trivial.
Qed.


Lemma EnvZip_none_1of2
 :  forall {A B} e1 e2 e12 n
 ,  EnvZip e1 e2 e12
 -> @lookupEnv A n e1 = None
 -> @lookupEnv B n e2 = None.
Proof.
 intros A B e1 e2 e12 n HZ HL1.
 induction HZ.
 - simpl in *.
   congruence.
 - simpl in *.
   remember (string_dec n n0) as X.
   destruct X.
   + congruence.
   + firstorder.
Qed.


Lemma EnvZip_none_2of1
 :  forall {A B} e1 e2 e12 n
 ,  EnvZip e1 e2 e12
 -> @lookupEnv A n e2 = None
 -> @lookupEnv B n e1 = None.
Proof.
 intros A B e1 e2 e12 n HZ HL2.
 induction HZ.
 - simpl in *.
   congruence.
 - simpl in *.
   remember (string_dec n n0) as X.
   destruct X.
   + congruence.
   + firstorder.
Qed.


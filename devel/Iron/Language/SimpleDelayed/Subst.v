
Require Export Coq.Strings.String.
Require Export LocalLibTactics.
Require Export LocalLibDataLists.


(********************************************************************)
(* Variables want to be named. *)
Definition name := string.


(********************************************************************)
(* Type signatures *)
Inductive  sig {A: Type}: Type :=
 | SSig  : name -> A -> @sig A.


(* An environment is a list of signatures. *)
Definition env (A: Type) 
 := list (@sig A).


(* Lookup the type of the given variable from an environment. *)
Fixpoint lookupEnv {T: Type} (var: string) (ee: env T) : option T :=
 match ee with
 | nil                
 => None

 | SSig v t :: rest
 => match string_dec var v with
    | left  _ => Some t
    | right _ => lookupEnv var rest
    end
 end.


(********************************************************************)
(* Typed bindings. *)
Inductive bind {X: Type} {T: Type}: Type :=
 | BBind   : name -> T -> X -> @bind X T.
Hint Constructors bind.


(* Get the type component of a binding. *)
Definition typeOfBind {X T} (b: @bind X T): T :=
 match b with
 | BBind _ t x => t
 end.


(* Get the expression component of a binding. *)
Definition expOfBind  {X T} (b: @bind X T): X :=
 match b with
 | BBind _ _ x => x
 end.


(* Apply a function to the expression component of a binding. *)
Definition mapExpOfBind {T X} 
  (f: X -> X) (b: @bind X T): @bind X T :=
 match b with
 | BBind n t x => BBind n t (f x)
 end.


(********************************************************************)
(* A substitution is a list of bindings. *)
Definition subst {X T} := list (@bind X T).


(* Apply a function to all the expression components of a list
   of bindings. *)
Definition mapExpOfSubst {X T}
  (f: X -> X) (bs: @subst X T): @subst X T := 
 map (mapExpOfBind f) bs.


(* Lookup the binding with the given name from a substitution. *)
Fixpoint lookupSubst {X T} 
   (var: string) (ss: @subst X T): option (@bind X T) :=
 match ss with
 |  nil                
 => None

 |  BBind v t x :: rest
 => match string_dec var v with 
    | left _  => Some (BBind v t x)
    | right _ => lookupSubst var rest
    end
 end.


(* When we lookup a binding with a particular name from a substitution, 
   then the returned binding has that name. *)
Lemma lookupSubst_name 
 :  forall {X T} n1 n2 t e bs
 ,  @lookupSubst X T n1 bs = Some (BBind n2 t e)
 -> n1 = n2.
Proof.
 intros.
 induction bs as [|b].
 - simpl in *. congruence.
 - simpl in *. destruct b.
   remember (string_dec n1 n) as d. destruct d.
   + inverts H. assumption.
   + firstorder.
Qed.


(********************************************************************)
(* Property is true of all pairs of expressions and types in a
   substitution. *)
Definition ForallSubstXT {X T} 
  (P: X -> T -> Prop) (ss: @subst X T): Prop :=
 Forall2 P (map expOfBind ss) (map typeOfBind ss).


(* Fold up a ForallSubstXT *)
Lemma ForallSubstXT_fold
 :  forall {X T} (P: X -> T -> Prop) (ss: @subst X T)
 ,  Forall2 P (map expOfBind ss) (map typeOfBind ss)
 -> ForallSubstXT P ss.
Proof.
 intros.
 eauto.
Qed.


(* ForallSubstXT append. *)
Lemma ForallSubstXT_app 
 :  forall {X T} (P: X -> T -> Prop) ss1 ss2
 ,  ForallSubstXT P ss1
 -> ForallSubstXT P ss2
 -> ForallSubstXT P (ss1 ++ ss2).
Proof.
 intros.
 unfold ForallSubstXT.
 eapply Forall2_map.
 eapply Forall2_app.
 - eapply Forall2_map'; auto.
 - eapply Forall2_map'; auto.
Qed.


(* Same as Forall2_mp, but keep the definition of
   ForallSubstXT folded. *)
Lemma ForallSubstXT_mp
 :  forall {X T} (P Q: X -> T -> Prop)        ss
 ,  ForallSubstXT (fun x t => P x t -> Q x t) ss
 -> ForallSubstXT (fun x t => P x t)          ss
 -> ForallSubstXT (fun x t => Q x t)          ss.
Proof.
 intros.
 eapply Forall2_mp; eauto.
Qed.


Lemma ForallSubstXT_mapExpOfSubst
 :  forall {X T} (f: X -> X) (P: X -> T -> Prop) (ss: @subst X T)
 ,  ForallSubstXT (fun x t => P (f x) t) ss
 -> ForallSubstXT (fun x t => P x t) (mapExpOfSubst f ss).
Proof.
 intros.
 unfold ForallSubstXT in *.
 induction ss as [|b].
 - simpl. auto.
 - simpl. inverts H.
   eapply Forall2_cons.
   + lets D: IHss H5.
     destruct b.
     simpl in *. assumption.
   + eauto. 
Qed.


(********************************************************************)
(* Strip the expression from a binding, producing a signature. *)
Fixpoint stripB {X T} (b: @bind X T): @sig T :=
 match b with
 | BBind n t _ => SSig n t
 end.


(* Strip a substitution to an environment. *)
Definition stripS {X T} (ss: @subst X T): @env T :=
 map stripB ss.
Hint Transparent stripS.


Lemma stripS_fold
 : forall {X T} ss
 , map (@stripB X T) ss = stripS ss.
Proof.
 eauto.
Qed.


(* Applying a function to the expressions of a substitution,
   then stripping it yields the same result as just stripping it. *)
Lemma stripS_mapExpOfSubst
 : forall {X T} f ss
 , @stripS X T (mapExpOfSubst f ss) = @stripS X T ss.
Proof.
 intros.
 induction ss as [|b].
 - simpl. auto.
 - simpl. rewrite IHss.
   destruct b. simpl. trivial.
Qed.


Lemma lookup_env_subst_none
 :  forall {X T} n te ss t
 ,  @lookupEnv     T n (stripS ss ++ te) = Some t
 -> @lookupSubst X T n ss                = None
 -> @lookupEnv     T n te                = Some t.
Proof.
 intros.
 induction ss as [|b].
 - simpl in *. assumption.
 - simpl in *. destruct b. simpl in H.
   remember (string_dec n n0) as d. destruct d.
   + inverts H. congruence.
   + eapply IHss. 
     * auto. 
     * assumption.
Qed.


Lemma lookup_env_subst_some
 :  forall {X T} n te ss e t1 t2 P
 ,  ForallSubstXT  P ss
 -> @lookupEnv     T n (stripS ss ++ te) = Some t1
 -> @lookupSubst X T n ss                = Some (BBind n t2 e)
 -> P e t1.
Proof.
 intros. gen n te e t1 t2.
 induction ss as [|b]; intros.
 - simpl in *. congruence.
 - simpl in *. destruct b. simpl in *.
   remember (string_dec n n0) as d. destruct d.
   + inverts H0. inverts H1.
     inverts H. assumption.
   + inverts H; eauto.
Qed.


Require Import Arith.
Require Import List.
Require Import Setoid.
Require Import Program.
Set Transparent Obligations.

(** {1 Type Algebra} *)

(** To simplify the technicalities, we focus on first-order types
    whose syntax is:

     τ := ι ∣ ι → τ

  They correspond to arities, i.e. natural numbers. Thus, we can
  denote them by the following function that computes Aⁿ → A. *)
Fixpoint type_of_arity (A : Type) n :=
  match n with
    | O => A
    | S n => A -> type_of_arity A n
  end.

(** Once a type A is inhabited, it is easy to write find an inhabitant
    for any type Aⁿ → A. *)
Fixpoint default_value {A} (default : A) k : type_of_arity A k :=
  match k with
      | O => default
      | S n => fun (x : A) => default_value default n
  end.

(** {1 Signatures} *)

(** A term constructor is assigned an arity n and an
    interpretation as coq term of type Aⁿ → A. *)
Definition constructor_signature A :=
  sigT (A := nat) (fun n => type_of_arity A n).

Definition mk_constructor {A} k (x : type_of_arity A k)
: constructor_signature A :=
  existT (fun n => type_of_arity A n) k x.

(** A constructor identifier is simply a natural number. *)
Definition constructor := nat.

(** A signature over A associates an arity and an interpretation
    to a list of constructors. *)
Definition signature A := list (constructor_signature A).

(** We implement a signature lookup as a total function
    producing [None] in case of failure. *)
Definition arity_descriptor := option nat.

Definition arity {A} (sgn : signature A) f : arity_descriptor :=
  match List.nth_error sgn f with
    | None => None
    | Some (existT _ k _) => Some k
  end.

(** [Find] is a predicate over signatures, arities and constructor
    interpretations. It denotes the property of an arity and an
    interpretation to be in a signature. *)
Class Find {A : Type}
  (sgn : signature A) (k : nat) (x : type_of_arity A k) := {
  (** The property is witnessed by the index of the pair in the
      signature. *)
  index          : nat;
  (** These equalities are useful to specialize total functions to
      the case where the arity and the constructor are in the
      signature. *)
  found          : nth_error sgn index = Some (mk_constructor k x);
  arity_of_index : arity sgn index = Some k
}.

(** [FindHead] is an instance of the predicate [Find] where the
    pair is at the beginning of the signature. *)
Program Instance FindHead {A : Type}
  (k : nat) (x : type_of_arity A k) (l : signature A) :
  (Find ((mk_constructor k x) :: l) k x) := {
  index := O
}.

(** [FindTail] is an instance of the predicate [Find where the
    pair is the tail of the signature. *)
Program Instance FindTail {A : Type}
  (k : nat)  (x : (type_of_arity A k))
  (l : nat) (y : (type_of_arity A l))
  (sgn : signature A)
  (Tail : Find sgn k x)
: (Find ((mk_constructor l y) :: sgn) k x) := {
  index := (S index);
  found := found
}.
Next Obligation.
  unfold arity. simpl. rewrite <- arity_of_index. unfold arity. reflexivity.
Defined.

(** As usual with index types, we need some coercion functions. This
    one is meant to convert a value of type Aⁿ → A into a value of
    type Aⁿ' → A if n = n'. *)
Lemma coerce_type_of_arity: forall A k k', k = k' ->
  type_of_arity A k -> type_of_arity A k'.
Proof.
  intros A k k' Hkk' H. now rewrite <- Hkk'.
Defined.

(** Apply an interpretation of arity k to a list of As. If the list of
    As is not of length k, then a default value is returned.  As for
    [arity], we artificially define a total function to avoid the use
    of too complex dependent types, which may be unpractical for "a
    posteriori" reasoning.  *)
Fixpoint apply
   {A} (default : A)
   (k : nat) (f : type_of_arity A k)
   (ts : list A)
: A :=
  match ts with
    | nil =>
      (match k return (type_of_arity A k -> A) with
        | O => fun x => x
        | _ => fun x => default
      end f)
    | cons x xs =>
        (match k return (type_of_arity A k -> A) with
          | O => fun _ => default
          | S k => fun (g : A -> type_of_arity A k) => apply default k (g x) xs
         end) f
  end.

Eval compute in (apply 0 2 (fun x y => x + y) (4 :: 5 :: nil)).

(** Finally, we are ready to define the interpretation
    of a constructor [f] of arity [k] in a signature [sgn]. *)
Definition constructor_interpretation {A}
  (default : A)
  (sgn : signature A) (f : constructor) (k : nat)
: type_of_arity A k
:=
match List.nth_error sgn f with
  | None => default_value default k
  | Some (existT _ k' x) =>
      match eq_nat_dec k' k with
        | left H => coerce_type_of_arity A k' k H x
        | _ => default_value default k
      end
end.

(** Apply a constructor [f] to a list of arguments by applying them to the
    the interpretation of [f] found in a given signature. *)
Definition apply_constructor {A}
  (default : A)
  (sgn : signature A)
  (f   : constructor)
  (ts  : list A)
: A :=
  match arity sgn f with
    | None => default
    | Some k => apply default k (constructor_interpretation default sgn f k) ts
  end.

(** {1 First order terms} *)

(** First order term are built from constructors applied to
    list of terms. This definition does not enforce the
    well-formedness of terms: a constructor may be applied
    to the wrong number of arguments. Yet, as we will reify
    well-typed Coq terms, this property is guaranteed
    at the meta-level. *)
Inductive term : Type :=
  | App : forall (f : constructor) (ts : list term),
    term.

(** A term is interpreted recursively using constructor interpretations. *)
Fixpoint term_interpretation {A} (default : A) (sgn : signature A) (t : term)
: A :=
  match t with
    | App f ts =>
        let xs := List.map (term_interpretation default sgn) ts in
          apply_constructor default sgn f xs
  end.

Example sgn1 : signature nat := [
    mk_constructor O 41;
    mk_constructor 1 S;
    mk_constructor 2 plus
  ].

Program Example t1 := App 1 (cons (App 0 nil) nil).

Compute (term_interpretation 0 sgn1 t1).

(** {1 Reification of first order terms} *)

(** A predicate stating that there exists a reification of [T]
    of type [A] as a first order term in the signature [sgn]. *)
Class ReifyTerm {A} (default : A) (sgn : signature A) (T : A) := {
  term_reification         : term;
  term_reification_correct : term_interpretation default sgn term_reification = T
}.

(** To define this predicate, we states an (incomplete) set of rules to
    syntactically catch Coq's terms of the form [F T₁ T₂ … T_n] for all
    n from 0 to a big enough constant (here we chose 3). *)

(** The proof of correctness for each of these
    rules is always the same: *)
Ltac sound_reification_rule :=
  unfold apply_constructor; rewrite arity_of_index;
  unfold constructor_interpretation;
  rewrite found; simpl; unfold coerce_type_of_arity;
  (repeat rewrite term_reification_correct); auto.

(** A rule for this predicate: a constant*)
Program Instance ReifyConstant {A} (default : A) (sgn : signature A)
  (T : A) (S : Find sgn 0 T) : ReifyTerm default sgn T := {
    term_reification := App (index (k := 0) (x := T)) nil
}.
Next Obligation. sound_reification_rule. Defined.

Program Instance ReifyApp1 {A} (default : A) (sgn : signature A)
  (F : A -> A) (FFind : Find sgn 1 F)
  (T : A) (RT : ReifyTerm default sgn T)
: ReifyTerm default sgn (F T) := {
   term_reification := App (index (k := 1) (x := F)) [ term_reification ]
}.
Next Obligation. sound_reification_rule. Defined.

Program Instance ReifyApp2 {A} (default : A) (sgn : signature A)
  (F : type_of_arity A 2) (FFind : Find sgn 2 F)
  (T1 : A) (RT1 : ReifyTerm default sgn T1)
  (T2 : A) (RT2 : ReifyTerm default sgn T2)
: ReifyTerm default sgn (F T1 T2) := {
   term_reification := App (index (k := 2) (x := F))
                           [ term_reification (T := T1);
                             term_reification (T := T2) ]
}.
Next Obligation. sound_reification_rule. Defined.

Program Instance ReifyApp3 {A} (default : A) (sgn : signature A)
  (F : type_of_arity A 3) (FFind : Find sgn 3 F)
  (T1 : A) (RT1 : ReifyTerm default sgn T1)
  (T2 : A) (RT2 : ReifyTerm default sgn T2)
  (T3 : A) (RT3 : ReifyTerm default sgn T3)
: ReifyTerm default sgn (F T1 T2 T3) := {
   term_reification := App (index (k := 3) (x := F))
                           [ term_reification (T := T1);
                             term_reification (T := T2);
                             term_reification (T := T3) ]
}.
Next Obligation. sound_reification_rule. Defined.

Compute (term_reification (sgn := sgn1) (default := 0)
                                  (T := plus 41 (S (S (S 41))))).

(** {1 Reification of congruence closure problem.} *)

(** An equality is a pair of two first-order terms. *)
Definition equality := (term * term)%type.

(** We interpret equalities using Coq's equality. *)
Definition equality_interpretation {A} (default : A) sgn (e : equality) :=
  let (x, y) := e in
    term_interpretation default sgn x = term_interpretation default sgn y.

(** A congruence closure problem is composed of an equality
    to prove and a list of equality to be used to achieve
    that goal. *)
Record problem := {
  hypothesis : list equality;
  goal       : equality
}.

(** The interpretation of hypotheses in a signature is the conjunction
    of the interpretation of the equalities. *)
Fixpoint conjunction_interpretation {A} (default : A) (sgn : signature A)
  (cs : list equality) :=
  match cs with
    | nil => True
    | e :: cs =>
        equality_interpretation default sgn e
     /\ conjunction_interpretation default sgn cs
  end.

(** A problem is interpreted as an implication. *)
Definition problem_interpretation {A} (default : A) (sgn : signature A)
  (p : problem) :=
  conjunction_interpretation default sgn (hypothesis p) ->
  equality_interpretation default sgn (goal p).

(** [assume p e] is [p] with an extra hypothesis [e]. *)
Definition assume (p : problem) (e : equality) : problem :=
{|
  hypothesis := e :: (hypothesis p);
  goal := goal p
|}.

(** A predicate stating that [P] has a reification in a signature [sgn]. *)
Class ProblemReification {A} (default : A) (sgn : signature A) (P : Prop) := {
  problem_reification : problem;
  problem_reification_correct :
  problem_interpretation default sgn problem_reification <-> P
}.

(** An equality is a goal for a problem with no hypothesis. *)
Program Instance problem_base {A} (default : A) (sgn : signature A)
  (x y : A)
  (xr : ReifyTerm default sgn x)
  (yr : ReifyTerm default sgn y)
: ProblemReification default sgn (x = y) := {
  problem_reification := {|
    hypothesis := nil;
    goal       := (term_reification (T := x), (term_reification (T := y)))
  |}
}.
Next Obligation.
  unfold problem_interpretation. simpl.
  repeat (rewrite term_reification_correct).
  tauto.
Defined.

(** An implication of the form [x = y ⇒ P] can be recursively reified. *)
Program Instance problem_hyp {A} (default : A) (sgn : signature A)
  (P : Prop)
  (x y : A)
  (xr : ReifyTerm default sgn x)
  (yr : ReifyTerm default sgn y)
  (RP : ProblemReification default sgn P)
:
  ProblemReification default sgn (x = y -> P)
:= {
  problem_reification :=
  assume problem_reification
         (term_reification (T := x), (term_reification (T := y)))
}.
Next Obligation.
  unfold problem_interpretation. simpl.
  repeat (rewrite term_reification_correct).
  generalize problem_reification_correct.
  intuition.
Defined.

Implicit Arguments problem_reification [A sgn ProblemReification].

Print Implicit problem_reification.

Example p1 :=
  (problem_reification (A := nat) (sgn := sgn1) 0
                       (41 = 41 -> S 41 = S 41)).

Compute p1.
Compute (problem_interpretation O sgn1 p1).

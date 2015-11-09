(** Congruence closure *)
Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Require Import OrderedType.
Require Import FSetAVL.
Require Import Cybele.Cybele.
Require Import Cybele.Map.
Require Import Cybele.DataStructures.
Require Import Definitions.

Set Implicit Arguments.
Set Transparent Obligation.
Import Monad ListNotations.

(** Example with only constants *)
Module ExampleNoFun.
  Require Import Algo.

  Module P <: Parameters.
    Definition T := nat.
    Definition Values :=
      let values := [3; 5; 5; 6; 3; 0; 5] in
      List.map (fun n => Value.Make 0 (fun _ => n)) values.
  End P.
  Module CC := CongruenceClosure P.
  Import CC.

  Definition IndexOfNat (i: nat): Index.t :=
    Index.Make i nil.

  Coercion IndexOfNat: nat >-> Index.t.

  Definition eq_proofs: list T.
    refine (
      EqProof.Make (i := 0) (j := 4) _ ::
      EqProof.Make (i := 1) (j := 2) _ ::
      EqProof.Make (i := 2) (j := 1) _ ::
      EqProof.Make (i := 2) (j := 6) _ ::
      nil);
    now unfold Values.AreEqual.
  Defined.

  Lemma Eq1: Values.AreEqual P.Values 0 4.
    now apply (proof_by_reflection (ProveEqual eq_proofs 0 4)
      (Prophecy.of_nat Sig 100)).
  Defined.

  Lemma Eq2: Values.AreEqual P.Values 1 6.
    now apply (proof_by_reflection (ProveEqual eq_proofs 1 6)
      (Prophecy.of_nat Sig 100)).
  Defined.
End ExampleNoFun.

(** Small example relying on congruence *)
Module ExampleCongruence.
  Require Import Algo.

  Module P <: Parameters.
    Definition T := nat.

    Definition Values: list (Value.t T) :=
      Value.Make 0 (fun _ => 3) ::
      Value.Make 1 (fun v =>
        match v with
        | x :: nil => 6 - x
        | _ => 0
        end) ::
      nil.
  End P.

  Module CC := CongruenceClosure P.
  Import CC.

  Definition a := Index.Make 0 nil.
  Definition fa := Index.Make 1 (a :: nil).
  Definition ffa := Index.Make 1 (fa :: nil).

  Fixpoint fn n :=
    match n with
      | O => a
      | S k => Index.Make 1 (fn k :: nil)
    end.

  Definition fbig : Index.t.
  let f := eval compute in (fn 50) in exact f.
  Defined.

  Definition eq_proofs: list T.
    refine (
      EqProof.Make (i := a) (j := fa) _ ::
      nil); now unfold Values.AreEqual.
  Defined.

  Definition eval (x y: Index.t) (nb_steps: nat) :=
    if fst (ProveEqual eq_proofs x y
      (State.of_prophecy (Prophecy.of_nat Sig nb_steps)))
    then true else false.

  Time Compute eval a a 1.
  Time Compute eval fa a 100.
  Time Compute eval fa ffa 100.
  Time Compute eval a fa 100.
  Time Compute eval fa fbig 100.

  Definition Equal (i j: Index.t) :=
    proof_by_reflection (ProveEqual eq_proofs i j) (Prophecy.of_nat Sig 100).

  Check Equal a a eq_refl.
  Check Equal a fa eq_refl.
  Check Equal a ffa eq_refl.
End ExampleCongruence.

(** Example from the Pierre Corbineau's master thesis *)
Module ExampleBig.
  Module P <: Parameters.
    Definition T := nat.

    Definition Values: list (Value.t T) :=
      Value.Make 0 (fun _ => 3) ::
      Value.Make 0 (fun _ => 1) ::
      Value.Make 1 (fun v =>
        match v with
        | x :: nil => 6 - x
        | _ => 0
        end) ::
      Value.Make 2 (fun v =>
        match v with
        | x :: y :: nil => x + y - 1
        | _ => 0
        end) ::
      nil.
  End P.

  Definition a := Index.Make 0 nil.
  Definition b := Index.Make 1 nil.
  Definition fa := Index.Make 2 (a :: nil).
  Definition gab := Index.Make 3 (a :: b :: nil).
  Definition fgba := Index.Make 2 (Index.Make 3 (b :: a :: nil) :: nil).
  Definition gbfa := Index.Make 3 (b :: fa :: nil).
  Definition ffa := Index.Make 2 (fa :: nil).

  Fixpoint f_n_a (n: nat) :=
    match n with
    | O => a
    | S n' => Index.Make 2 [f_n_a n']
    end.

  Check eq_refl: Values.NthIndex P.Values a = Some 3.
  Check eq_refl: Values.NthIndex P.Values fa = Some 3.
  Check eq_refl: Values.NthIndex P.Values ffa = Some 3.
  Check eq_refl: Values.NthIndex P.Values fgba = Some 3.

  Module GenerateProofs.
    Require Import Algo.
    Module CC := CongruenceClosure P.
    Import CC.

    Definition eq_proofs: list T.
      refine (
        EqProof.Make (i := a) (j := fa) _ ::
        EqProof.Make (i := gab) (j := fgba) _ ::
        EqProof.Make (i := gbfa) (j := ffa) _ ::
        EqProof.Make (i := gab) (j := a) _ ::
        nil); now unfold Values.AreEqual.
    Defined.

    Definition compute (i j: Index.t): bool :=
      is_computable (ProveEqual eq_proofs i j) (Prophecy.of_nat Sig 100).

    Time Compute compute a fa.
    Time Compute compute gab a.
    Time Compute compute (f_n_a 200) a.

    Definition equal (i j: Index.t) :=
      proof_by_reflection (ProveEqual eq_proofs i j) (Prophecy.of_nat Sig 100).

    Time Check equal a a eq_refl.
    Time Check equal a fa eq_refl.
    Time Check equal a ffa eq_refl.
    Time Fail Check equal a b eq_refl.
    Time Check equal gab a eq_refl.

    Lemma Eq1: Values.AreEqual P.Values a ffa.
      apply (proof_by_reflection (ProveEqual eq_proofs a ffa)
        (Prophecy.of_nat Sig 100)).
      now vm_compute.
    Defined.

    Lemma Eq2: Values.AreEqual P.Values gab a.
      apply (proof_by_reflection (ProveEqual eq_proofs gab a)
        (Prophecy.of_nat Sig 100)).
      now vm_compute.
    Defined.
  End GenerateProofs.

  Module JustDecide.
    Require Import AlgoBool.
    Module CC := CongruenceClosureBool P.
    Import CC.

    Definition eq_proofs: list T.
      refine (
        EqProof.Make (i := a) (j := fa) _ ::
        EqProof.Make (i := gab) (j := fgba) _ ::
        EqProof.Make (i := gbfa) (j := ffa) _ ::
        EqProof.Make (i := gab) (j := a) _ ::
        nil); now unfold Values.AreEqual.
    Defined.

    Definition compute (i j: Index.t): bool :=
      is_computable (ProveEqual eq_proofs i j) (Prophecy.of_nat Sig 100).

    Time Compute compute a fa.
    Time Compute compute gab a.
    Time Compute compute (f_n_a 200) a.

    Definition equal (i j: Index.t) :=
      proof_by_reflection (ProveEqual eq_proofs i j) (Prophecy.of_nat Sig 100).

    Time Check equal a a eq_refl.
    Time Check equal a fa eq_refl.
    Time Check equal a ffa eq_refl.
    Time Fail Check equal a b eq_refl.
    Time Check equal gab a eq_refl.
  End JustDecide.
End ExampleBig.

Require Import Arith.
Require Import OrderedTypeEx.
Require Import FMapAVL.
Require Import FMapInterface.
Require Import Cybele.Cybele.
Require Import Cybele.Reifiable.
Require Import Cybele.Memoization.
Import Monad.

Module NatMap := FMapAVL.Make Nat_as_OT.
Module RNatMap := Reifiable.Map NatMap.

Definition ReifiableNatMap :=
  RNatMap.Map Reifiable.Nat Reifiable.Nat.

Definition sig := Sig.Make
  (existT _ _ (Reifiable.List Reifiable.Nat) ::
  existT _ _ ReifiableNatMap :: nil)
  nil.

Definition fact: nat -> M sig nat :=
  fun n =>
  letrec! aux [ fun k => nat ] := fun (k: nat) =>
    match k with
      | O => ret (S O)
      | S i =>
        let! y := aux i in
          ret (k * y)
    end
  in
  aux n.

Set Extraction AccessOpaque.

(*Lemma fact1: nat.
  cybele (fact 1).
Defined.
Print fact1.

Lemma fact2: nat. cybele (fact 5). Defined. Print fact2.*)

Module NatMemo := InputMemo NatMap.

Definition memo: NatMemo.t _ _ := input_ref sig 1 (NatMap.empty _).

Definition memo_fact: nat -> M sig nat :=
  NatMemo.memoize memo fact.

Lemma fact3: nat * nat.
  cybele (
    let! n1 := memo_fact 3 in
    let! n2 := memo_fact 5 in
    ret (n1, n2)).
Defined.
Print fact3.

Definition trace: Trace.t _ _ := input_ref sig 0 nil.

Definition eval_fact: nat -> M sig nat :=
  fun n =>
    Trace.eval trace (fun _ => fact n).

(** Factorial with trace pre-evaluation *)
Lemma fact4: nat * nat.
  cybele (
    let! n1 := eval_fact 3 in
    let! n2 := eval_fact 5 in
    ret (n1, n2)).
Defined.
Print fact4.

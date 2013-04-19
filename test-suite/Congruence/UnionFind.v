(** Just an union-find *)
Require Import Arith.Peano_dec.
Require Import String.
Require Import List.
Require Import Cybele.
Require Import Cybele.DataStructures.

Set Implicit Arguments.
Set Transparent Obligation.
Import Monad ListNotations.

(** Normal union-find with array of integers *)
Module UnionFind.
  Definition Sig: Sig.t := Sig.Make nil ((Array.internal_t nat: Type) :: nil).
  Definition Array := Array.t Sig nat.
  Definition M := M Sig.
  
  (** The representative of [i] *)
  Definition Find (array: Array) (i: nat): M nat :=
    fix_ (fun f i =>
      let! j := Array.read array i in
      match eq_nat_dec i j with
      | left _ => ret i
      | right _ => f j
      end) i.
  
  (** Merge the equivalent classes of [i] and [j] *)
  Definition Unify (array: Array) (i j: nat): M unit :=
    let! i' := Find array i in
    let! j' := Find array j in
    Array.write array i' j'.
  
  (** Do the union-find with a list of equalities and return
      the list of representatives *)
  Definition UnionFind (n: nat) (unions: list (nat * nat))
    : M (list nat) :=
    let! array := tmp_ref Sig 0 (seq 0 n) in
    do! List.iter (fun (ij: nat * nat) =>
      let (i, j) := ij in
      Unify array i j)
      unions in
    Array.to_list array.
  
  Definition Eval (n: nat) (l: list (nat * nat)) (nb_steps: nat) :=
    UnionFind n l (State.of_prophecy (Prophecy.of_nat _ nb_steps)).
  
  Compute Eval 10 nil 0.
  Compute Eval 10 [(0, 1); (0, 0); (2, 9); (1, 4); (4, 1)] 2.
End UnionFind.
Require Import Coqbottom.
Require Import Coqbottom.Reifiable.
Import Monad.

Definition sig1 := Sig.Make nil ((nat: Type) :: nil).

Definition sum (n m: nat): M sig1 nat :=
  let! s := tmp_ref sig1 0 n in
  let! s' := !s in
  do! s :=! s' + m in
  !s.

Compute sum 2 3 (State.of_prophecy (Prophecy.of_nat sig1 0)).

Lemma sum1: nat.
  coq (sum 2 3).
Defined.
Print sum1.

Definition sig2 := Sig.Make (existT _ _ Reifiable.Nat :: nil) nil.

Definition input: M sig2 nat :=
  let s := input_ref sig2 0 3 in
  do! s :=! 5 in
  !s.

Lemma input1: nat.
  coq input.
Defined.
Print input1.

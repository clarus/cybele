Require Import NPeano.
Require Import Lattice.
Require Import Algo.
Require Import Cybele.
Import Monad.

(** * Lattices examples *)
(** We need to instanciate a specific lattice to have a complete
    extraction; here the lattice of natural numbers *)
Module P <: Lattice.Param.
  Definition A := nat.
  
  Definition Lattice: Lattice.t A.
    refine (Lattice.New min max
      Nat.min_id Nat.min_comm _ Nat.max_min_absorption
      Nat.max_id Nat.max_comm _ Nat.min_max_absorption); intros.
      now rewrite Nat.min_assoc.
      
      now rewrite Nat.max_assoc.
  Defined.
End P.

Module Lattice := Lattice.Instance P.
Module Algo := Algo P.
Import P Lattice.Notations Algo.
Local Open Scope lattice_scope.

Set Extraction AccessOpaque.


(** Small examples are solved without compilation to OCaml since extraction
    can be very slow with the full Map library. *)
Lemma easy: forall x y, x /*\ y <= y \*/ x.
  intros; Reify Only.
  apply (proof_by_reflection (ProveLeq false (term1, term2))
    (Prophecy.of_nat Sig 100)).
  now vm_compute.
Defined.

Lemma median: forall x y z,
  (x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x) <=
  (x \*/ y) /*\ (y \*/ z) /*\ (z \*/ x).
  intros; Reify Only.
  apply (proof_by_reflection (ProveLeq false (term1, term2))
    (Prophecy.of_nat Sig 100)).
  now vm_compute.
Defined.


(** ** Performance tests *) 

Definition gas := 10000.

Ltac solve_without_ocaml term1 term2 :=
  apply (proof_by_reflection (ProveLeq false (term1, term2))
    (Prophecy.of_nat Sig gas));
  vm_compute.

(** *** Exponential cases. *)

(** Without compiling to Ocaml. *)

Lemma nc_ex1: forall
  (x00 x01 x02 x03 x04
  y00 y01 y02 y03 y04 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ x04.
  idtac "nc_ex1".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex2: forall
  (x00 x01 x02 x03 x04 x05
  y00 y01 y02 y03 y04 y05 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ x05.
  idtac "nc_ex2".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex3: forall
  (x00 x01 x02 x03 x04 x05 x06
  y00 y01 y02 y03 y04 y05 y06 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ x06.
  idtac "nc_ex3".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex4: forall
  (x00 x01 x02 x03 x04 x05 x06 x07
  y00 y01 y02 y03 y04 y05 y06 y07 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ x07  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ x07.
  idtac "nc_ex4".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex5: forall
  (x00 x01 x02 x03 x04 x05 x06 x07 x08
  y00 y01 y02 y03 y04 y05 y06 y07 y08 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ x07 /*\ x08  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ y07 \*/ x08.
  idtac "nc_ex5".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex6: forall
  (x00 x01 x02 x03 x04 x05 x06 x07 x08 x09
  y00 y01 y02 y03 y04 y05 y06 y07 y08 y09 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ x07 /*\ x08 /*\ x09  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ y07 \*/ y08 \*/ x09.
  idtac "nc_ex6".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex7: forall
  (x00 x01 x02 x03 x04 x05 x06 x07 x08 x09 x10
  y00 y01 y02 y03 y04 y05 y06 y07 y08 y09 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ x07 /*\ x08 /*\ x09 /*\ x10 <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ y07 \*/ y08 \*/ y09 \*/ x10.
  idtac "nc_ex7".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.


(** With extraction to OCaml and branch memoization. *)

Lemma ex1: forall
  (x00 x01 x02 x03 x04
  y00 y01 y02 y03 y04 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ x04.
  idtac "ex1".
  Time intros; Reify Solve.
Time Defined.

Lemma ex2: forall
  (x00 x01 x02 x03 x04 x05
  y00 y01 y02 y03 y04 y05 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ x05.
  idtac "ex2".
  Time intros; Reify Solve.
Time Defined.

Lemma ex3: forall
  (x00 x01 x02 x03 x04 x05 x06
  y00 y01 y02 y03 y04 y05 y06 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ x06.
  idtac "ex3".
  Time intros; Reify Solve.
Time Defined.

Lemma ex4: forall
  (x00 x01 x02 x03 x04 x05 x06 x07
  y00 y01 y02 y03 y04 y05 y06 y07 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ x07  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ x07.
  idtac "ex4".
  Time intros; Reify Solve.
Time Qed.

Lemma ex5: forall
  (x00 x01 x02 x03 x04 x05 x06 x07 x08
  y00 y01 y02 y03 y04 y05 y06 y07 y08 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ x07 /*\ x08  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ y07 \*/ x08.
  idtac "ex5".
  Time intros; Reify Solve.
Time Qed.

Lemma ex6: forall
  (x00 x01 x02 x03 x04 x05 x06 x07 x08 x09
  y00 y01 y02 y03 y04 y05 y06 y07 y08 y09 : A),
  x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ x07 /*\ x08 /*\ x09  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ y07 \*/ y08 \*/ x09.
  idtac "ex6".
  Time intros; Reify Solve.
Time Qed.



(** *** Examples with repetition patterns *)


(** Not extracting to Ocaml. *)

Lemma nc_ex_with_repetitions02: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "nc_ex_with_repetitions02".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex_with_repetitions03: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "nc_ex_with_repetitions03".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex_with_repetitions04: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "nc_ex_with_repetitions04".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.

Lemma nc_ex_with_repetitions05: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "nc_ex_with_repetitions05".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.


Lemma nc_ex_with_repetitions06: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "nc_ex_with_repetitions06".
  Time intros; Reify Only;
    now solve_without_ocaml term1 term2.
Time Qed.


(** Extracting to Ocaml. *)

Lemma with_repetitions02: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "with_repetitions02".
  Time intros; Reify Solve.
Time Qed.

Lemma ex_with_repetitions03: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "ex_with_repetitions03".
  Time intros; Reify Solve.
Time Qed.

Lemma ex_with_repetitions04: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "ex_with_repetitions04".
  Time intros; Reify Solve.
Time Qed.

Lemma ex_with_repetitions05: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "ex_with_repetitions05".
  Time intros; Reify Solve.
Time Qed.


Lemma ex_with_repetitions06: forall
  (x00 x01 x02 x03 x04 x05 x06
   y00 y01 y02 y03 y04 y05 y06
   z00 : A),
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00) \*/
  (x00 /*\ x01 /*\ x02 /*\ x03 /*\ x04 /*\ x05 /*\ x06 /*\ z00)
  <=
  y00 \*/ y01 \*/ y02 \*/ y03 \*/ y04 \*/ y05 \*/ y06 \*/ z00.
  idtac "ex_with_repetitions06".
  Time intros; Reify Solve.
Time Qed.

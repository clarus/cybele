(** Solve goals about equivalences *)
Require Import Arith.Peano_dec.
Require Import String.
Require Import List.
Require Import Relations.
Require Import Cybele.
Require Import Cybele.DataStructures.

Set Implicit Arguments.
Set Transparent Obligation.
Import Monad ListNotations.

(** Decide if two elements are equivalent according to some known equivalence properties *)
Section EquivalenceDecision.
  Variable T : Type.
  Variable R : relation T.
  Variable Hequiv : equivalence _ R.
  Variable eq_dec : forall x y : T, { x = y } + { x <> y }.
  Infix "~" := R (at level 70, no associativity).
  
  (** An [equality] is a proof of equivalence plus these two equivalent elements *)
  Definition equality := {ij : T * T | fst ij ~ snd ij}.
  Definition equalities := list equality.
  Definition s : Sig.t := Sig.Make nil [equalities].
  Definition M := M s.
  
  (** Read in an equality list *)
  Fixpoint read (eqs : equalities) (i : T) {struct eqs} : option {j : T | i ~ j}.
    refine (
      match eqs with
      | nil => None
      | exist _ i'j Hi'j :: eqs' =>
        if eq_dec i (fst i'j)
        then Some (exist _ (snd i'j) _)
        else read eqs' i
      end).
    congruence.
  Defined.
  
  (** Write in an equality list; add a new element if [i] is not found *)
  Fixpoint write (eqs : equalities) (i : T) (Pj : {j : T | i ~ j}) : equalities.
    refine (
      match eqs with
      | nil =>
        let (j, Hij) := Pj in
        [exist _ (i, j) _]
      | (exist _ i'j' Hi'j') as x :: eqs' =>
        if eq_dec i (fst i'j') then
          let (j, Hij) := Pj in
          exist _ (i, j) _ :: eqs'
        else
          x :: write eqs' i Pj
      end);
    trivial.
  Defined.
  
  (** Find the representative of [i]; add the equivalence of [i] with [i]
      if [i] is not in [r] *)
  Definition find (r : Ref.t s equalities) (i : T) : M {j : T | i ~ j}.
    refine (
      dependent_fix (fun i => {j : T | i ~ j}) (fun aux i =>
        let! eqs := !r in
        match read eqs i with
        | None =>
          let Pi := exist _ i _ in
          do! r :=! write eqs Pi in
          ret Pi
        | Some Pj =>
          let (j, Hij) := Pj in
          if eq_dec i j then
            ret (exist _ j _)
          else
            let! Pk := aux j in
            let (k, Hjk) := Pk in
            ret (exist _ k _)
        end) i); trivial.
    now apply (equiv_trans _ _ Hequiv _ j).
    
    now apply (equiv_refl _ _ Hequiv).
  Defined.
  
  (** Merge two equivalent classes according to [eq] *)
  Definition unify (r : Ref.t s equalities) (eq : equality) : M unit.
    refine (
      let (ij, Hij) := eq in
      let! Pi' := find r (fst ij) in
      let (i', Hii') := Pi' in
      let! Pj' := find r (snd ij) in
      let (j', Hjj') := Pj' in
      let! eqs := !r in
      r :=! write eqs (i := i') (exist _ j' _)).
    apply (equiv_trans _ _ Hequiv _ (fst ij)).
      now apply (equiv_sym _ _ Hequiv).
      
      now apply (equiv_trans _ _ Hequiv _ (snd ij)).
  Defined.
  
  (** Decide if [i] and [j] are equivalent doing an union-find *)
  Definition decide (known_eqs : equalities) (i j : T) : M (i ~ j).
    refine (
      let! r := tmp_ref s 0 nil in
      do! List.iter (unify r) known_eqs in
      let! Pi' := find r i in
      let (i', Hii') := Pi' in
      let! Pj' := find r j in
      let (j', Hjj') := Pj' in
      if eq_dec i' j' then
        ret _
      else
        error "decide: the terms are not equal").
    apply (equiv_trans _ _ Hequiv _ i'); trivial.
    apply (equiv_trans _ _ Hequiv _ j').
      replace i' with j'.
      now apply (equiv_refl _ _ Hequiv).
      
      now apply (equiv_sym _ _ Hequiv).
  Defined.
End EquivalenceDecision.

(** An example with arithmetic formulæ *)
Module Example.
  Inductive t :=
  | const : nat -> t
  | add : t -> t -> t.
  
  Scheme Equality for t.
  
  Fixpoint eval (e : t) : nat :=
    match e with
    | const n => n
    | add e1 e2 => eval e1 + eval e2
    end.
  
  Definition R e1 e2 := eval e1 = eval e2.
  Infix "~" := R (at level 70, no associativity).
  
  Definition Hequiv : equivalence _ R.
    refine (Build_equivalence _ R _ _ _); congruence.
  Qed.
  
  Lemma equiv_add_zero : forall (e : t), e ~ add e (const 0).
    intro e.
    unfold R.
    now simpl.
  Qed.
  
  Fixpoint add_n_zero e n : t :=
    match n with
    | O => e
    | S n' => add (add_n_zero e n') (const 0)
    end.
  
  Definition known_eqs (e : t) (n : nat) : equalities R.
    refine (
      map (fun i =>
        exist _ (add_n_zero e i, add_n_zero e (S i)) _)
        (seq 0 n)).
    simpl.
    now apply equiv_add_zero.
  Defined.
  
  Definition decide_bool known_eqs e1 e2 nb_steps : bool :=
    is_computable (decide Hequiv t_eq_dec known_eqs e1 e2)
      (Prophecy.of_nat _ nb_steps).
  
  Definition four := const 4.
  Definition ten := const 10.
  Definition ten' := add (const 5) (const 5).
  
  Definition eq_ten_ten' : equality R.
    exists (ten, ten').
    unfold R; now simpl.
  Defined.
  
  Compute decide_bool (known_eqs four 10)
    (add_n_zero four 0) (add_n_zero four 8) 100.
  
  Compute decide_bool (known_eqs four 100)
    (add_n_zero four 0) (add_n_zero four 100) 1000.
  Compute decide_bool (known_eqs four 100)
    (add_n_zero four 0) (add_n_zero four 101) 1000.
  Compute decide_bool (known_eqs ten 100)
    (add_n_zero four 0) (add_n_zero four 100) 1000.
  
  Compute decide_bool (known_eqs ten 100 ++ known_eqs ten' 100)
    (add_n_zero ten 0) (add_n_zero ten' 100) 1000.
  Compute decide_bool (eq_ten_ten' :: known_eqs ten 100 ++ known_eqs ten' 100)
    (add_n_zero ten 0) (add_n_zero ten' 100) 1000.
End Example.
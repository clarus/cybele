(** Reification is the mechanism used to transmit values from OCaml to Coq. *)
Require Import Setoid.
Require Import NArith.
Require Import PArith.
Require Import Map.

Set Implicit Arguments.

(** A S-expression, basically a binary tree, can reify almost any data value. *)
Module SExpr.
  Inductive t: Type :=
  | I: t
  | B: t -> t -> t.
End SExpr.

(** A reifiable type is a type equipped with reification functions. *)
Module Reifiable.
  Import SExpr.

  Record t (T: Type): Type := New {
    Export: T -> SExpr.t;
    Import: SExpr.t -> T}.

  (** We expect to get the original value from a reified one. *)
  Definition IsSound (T: Type) (r: t T): Prop :=
    forall (v: T), Import r (Export r v) = v.

  (** If we can reify [A] to [B] and reify [B], then we can reify [A]. *)
  Definition Morphism (A B: Type) (r: t B)
    (export: A -> B) (import: B -> A): t A := New
    (fun a => Export r (export a))
    (fun s => import (Import r s)).

  (** [unit] is reifiable. *)
  Definition Unit: t unit := New
    (fun _ => I)
    (fun _ => tt).

  (** [bool] is reifiable. *)
  Definition Bool: t bool := New
    (fun b =>
      match b with
      | false => I
      | true => B I I
      end)
    (fun s =>
      match s with
      | I => false
      | _ => true
      end).

  (** [positive] is reifiable. *)
  Definition BinPos: t positive := New
    (fix export n :=
      match n with
      | xH => I
      | xO n' => B I (export n')
      | xI n' => B (B I I) (export n')
      end)
    (fix import s :=
      match s with
      | I => xH
      | B I s' => xO (import s')
      | B _ s' => xI (import s')
      end).

  (** [N] is reifiable. *)
  Definition BinNat: t N := New
    (fun n =>
      match n with
      | N0 => I
      | Npos pos => B I (Export BinPos pos)
      end)
    (fun s =>
      match s with
      | I => N0
      | B _ s' => Npos (Import BinPos s')
      end).

  (** [nat] is reifiable. We do a binary encoding. *)
  Definition Nat: t nat :=
    Morphism BinNat N.of_nat N.to_nat.

  (** A product type is reifiable. *)
  Definition Product (T1 T2: Type) (r1: t T1) (r2: t T2)
    : t (T1 * T2) := New
    (fun v =>
      B (Export r1 (fst v)) (Export r2 (snd v)))
    (fun s =>
      match s with
      | I => (Import r1 I, Import r2 I)
      | B s1 s2 => (Import r1 s1, Import r2 s2)
      end).

  (** A sum type is reifiable. *)
  Definition Sum (T1 T2: Type) (r1: t T1) (r2: t T2)
    : t (T1 + T2) := New
    (fun v =>
      match v with
      | inl v' => B I (Export r1 v')
      | inr v' => B (B I I) (Export r2 v')
      end)
    (fun v =>
      match v with
      | I => inl (Import r1 I)
      | B I s' => inl (Import r1 s')
      | B _ s' => inr (Import r2 s')
      end).

  (** A list is reifiable. *)
  Definition List (T: Type) (r: t T)
    : t (list T) := New
    (fix export v :=
      match v with
      | nil => I
      | cons x v' => B (Export r x) (export v')
      end)
    (fix import s :=
      match s with
      | I => nil
      | B s1 s2 => cons (Import r s1) (import s2)
      end).

  (** A map is reifiable. *)
  Module Map (Map: IMap).
    Definition Map (T: Type) (r_key: t Map.key) (r: t T)
      : t (Map.t T) := Morphism
      (List (Product r_key r))
      (fun map =>
        Map.fold (fun k v l => cons (k, v) l) map nil)
      (fun l =>
        List.fold_left (fun map (kv: _ * _) =>
          let (k, v) := kv in
          Map.add k v map) l (Map.empty _)).
  End Map.

  (** The above definitions are sound. *)
  Module Facts.
    Lemma MorphismIsSound: forall (A B: Type) (r: t B)
      (export: A -> B) (import: B -> A),
      (forall (v: A), import (export v) = v) -> IsSound r ->
      IsSound (Morphism r export import).
      intros A B r export import Ha Hr v.
      simpl.
      now rewrite Hr.
    Qed.

    Lemma UnitIsSound: IsSound Unit.
      intro v.
      now destruct v.
    Qed.

    Lemma BoolIsSound: IsSound Bool.
      intro v.
      now destruct v.
    Qed.

    Lemma BinPosIsSound: IsSound BinPos.
      intro v.
      induction v; trivial;
      now rewrite <- IHv at 2.
    Qed.

    Lemma BinNatIsSound: IsSound BinNat.
      intro v.
      destruct v; trivial.
      simpl.
      now rewrite BinPosIsSound.
    Qed.

    Lemma NatIsSound: IsSound Nat.
      intro v.
      unfold Nat.
      rewrite MorphismIsSound; trivial.
        exact Nat2N.id.

        exact BinNatIsSound.
    Qed.

    Lemma ProductIsSound: forall (T1 T2: Type) (r1: t T1) (r2: t T2),
      IsSound r1 -> IsSound r2 -> IsSound (Product r1 r2).
      intros T1 T2 r1 r2 H1 H2 v.
      destruct v as [v1 v2].
      simpl.
      now rewrite H1; rewrite H2.
    Qed.

    Lemma SumIsSound: forall (T1 T2: Type) (r1: t T1) (r2: t T2),
      IsSound r1 -> IsSound r2 -> IsSound (Sum r1 r2).
      intros T1 T2 r1 r2 H1 H2 v.
      destruct v as [v1 | v2]; simpl.
        now rewrite H1.

        now rewrite H2.
    Qed.

    Lemma ListIsSound: forall (T: Type) (r: t T),
      IsSound r -> IsSound (List r).
      intros T r H v.
      induction v; trivial.
      rewrite <- IHv at 2.
      simpl.
      now rewrite H.
    Qed.
  End Facts.
End Reifiable.

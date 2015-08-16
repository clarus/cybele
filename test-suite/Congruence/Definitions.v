(** Congruence closure *)
Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Require Import OrderedType.
Require Import FSetAVL.
Require Import Cybele.
Require Import Cybele.Map.
Require Import Cybele.DataStructures.

Set Implicit Arguments.
Set Transparent Obligation.
Import Monad ListNotations.

(** Some usefull functions on the [option] type *)
Module Option.
  (** Monadic bind *)
  Definition Bind (A B: Type) (x: option A) (f: A -> option B): option B :=
    match x with
    | None => None
    | Some x' => f x'
    end.

  (** Destruct to eliminate a bind in a goal *)
  Ltac DestructBind v :=
    match goal with
    | [ |- context[Bind ?X _] ] => destruct X as [v |]
    end.

  (** Case_eq to eliminate a bind in a goal *)
  Ltac CaseBind v HNone :=
    match goal with
    | [ |- context[Bind ?X _] ] => case_eq X; [intro v | intro HNone]
    end.
End Option.

(** Values manipulated by the congruence-closure algorithm *)
Module Value.
  (** A value is a function on lists with an expected arity *)
  Record t (T: Type):= Make {
    Arity: nat;
    Value: list T -> T}.
End Value.

(** Index to reference values *)
Module Index.
  (** A index is a tree of integers used as indexes in a list of values *)
  Inductive t :=
  | Make: forall (i: nat), list t -> t.

  (** Induction principle for mutual recursion with indexes and lists *)
  Definition RecT (T: t -> Type) (Ts: list t -> Type)
    (f: forall (i: nat) (xs: list t), Ts xs -> T (Make i xs))
    (fnil: Ts nil)
    (fcons: forall (x: t) (xs: list t), T x -> Ts xs -> Ts (x :: xs))
    (x: t): T x :=
    let fix aux (x: t): T x :=
      let fix auxs (xs: list t): Ts xs :=
        match xs with
        | nil => fnil
        | x :: xs' => fcons x xs' (aux x) (auxs xs')
        end in
      match x with
      | Make i xs => f i xs (auxs xs)
      end in
    aux x.

  (** Induction principle for indexes and lists of indexes *)
  Definition DoubleRecT (T: t -> Type) (Ts: list t -> Type)
    (f: forall (i: nat) (xs: list t), Ts xs -> T (Make i xs))
    (fnil: Ts nil)
    (fcons: forall (x: t) (xs: list t), T x -> Ts xs -> Ts (x :: xs))
    : (forall (x: t), T x) * (forall (xs: list t), Ts xs) :=
    let aux (x: t): T x :=
      RecT T Ts f fnil fcons x in
    let fix auxs (xs: list t): Ts xs :=
      match xs with
      | nil => fnil
      | x :: xs' => fcons x xs' (aux x) (auxs xs')
      end in
    (aux, auxs).

  (** If two indexes are equal *)
  Fixpoint eqb (x y: Index.t): bool :=
    let fix eqbs (xs ys: list Index.t): bool :=
      match (xs, ys) with
      | (nil, nil) => true
      | (x :: xs', y :: ys') => andb (eqb x y) (eqbs xs' ys')
      | _ => false
      end in
    match (x, y) with
    | (Make i xs, Make j ys) => andb (NPeano.Nat.eqb i j) (eqbs xs ys)
    end.

  (** Decidability of equality on indexes *)
  Module MiniOrdered <: MiniOrderedType.
    Definition t := t.

    Definition eq := eq (A := t).

    Definition eq_refl := eq_refl (A := t).
    Definition eq_sym := eq_sym (A := t).
    Definition eq_trans := eq_trans (A := t).

    Definition lt_aux :=
      DoubleRecT
        (fun _ => t -> Prop)
        (fun _ => list t -> Prop)
        (fun i xs fxs y =>
          let (j, ys) := y in
          i < j \/ (i = j /\ fxs ys))
        (fun ys => ys <> nil)
        (fun x xs fx fxs ys =>
          match ys with
          | nil => False
          | y :: ys' => fx y \/ (x = y /\ fxs ys')
          end).

    Definition lt: t -> t -> Prop := fst lt_aux.
    Definition lts: list t -> list t -> Prop := snd lt_aux.

    Ltac destructLt Hxy Hij Hxsys :=
      destruct Hxy as [Hij | Hxsys]; [| destruct Hxsys as [Hij Hxsys]].

    Ltac destructLts Hxsys Hxy :=
      destruct Hxsys as [Hxy | Hxsys]; [| destruct Hxsys as [Hxy Hxsys]].

    Lemma lt_trans: forall (x y z: t), lt x y -> lt y z -> lt x z.
      refine (RecT
        (fun x => forall (y z: t), lt x y -> lt y z -> lt x z)
        (fun xs => forall (ys zs: list t), lts xs ys -> lts ys zs -> lts xs zs)
        (fun i xs Pxs y z Hxy Hyz => _)
        (fun ys zs Hnil Hyszs => _)
        (fun x xs Px Pxs ys zs Hxsys Hyszs => _)).
        destruct y as [j ys]; destruct z as [k zs].
        destructLt Hxy Hij Hxsys; destructLt Hyz Hjk Hyszs;
          try (left; omega).
        right; split; [congruence |].
        apply (Pxs _ _ Hxsys Hyszs).

        destruct ys as [| y ys].
          unfold lts in Hnil; simpl in Hnil.
          congruence.

          destruct zs as [| z zs]; [destruct Hyszs | congruence].

        destruct ys as [| y ys]; destruct zs as [| z zs]; trivial.
          destruct Hxsys.

          destructLts Hxsys Hxy; destructLts Hyszs Hyz;
            try (left; congruence).
            left; apply (Px _ _ Hxy Hyz).

            right; split; [congruence | apply (Pxs _ _ Hxsys Hyszs)].
    Defined.

    Lemma lt_not_eq: forall (x y: t), lt x y -> x <> y.
      refine (RecT
        (fun x => forall (y: t), lt x y -> x <> y)
        (fun xs => forall (ys: list t), lts xs ys -> xs <> ys)
        (fun i xs Pxs y Hxy => _)
        (fun ys Hnil => _)
        (fun x xs Px Pxs ys Hxsys => _)).
        destruct y as [j ys].
        destructLt Hxy Hij Hxsys.
          assert (i <> j); intro H'ij.
            rewrite H'ij in Hij.
            apply (lt_irrefl _ Hij).
          congruence.

          assert (Hxsys' := Pxs _ Hxsys).
          congruence.

        destruct ys as [| y ys]; trivial.
        congruence.

        destruct ys as [| y ys].
          congruence.

          destructLts Hxsys Hxy.
            assert (Hxy' := Px _ Hxy); congruence.

            assert (Hxsys' := Pxs _ Hxsys); congruence.
    Defined.

    Definition compare: forall (x y: t), Compare lt eq x y.
      refine (RecT
        (fun x => forall y, Compare lt eq x y)
        (fun xs => forall ys, Compare lts (Logic.eq (A := list t)) xs ys)
        (fun i xs Hxs y =>
          match y with
          | Make j ys =>
            match lt_eq_lt_dec i j with
            | inleft (left Hij) => LT _
            | inleft (right Hij) =>
              match Hxs ys with
              | LT Hxs => LT _
              | EQ Hxs => EQ _
              | GT Hxs => GT _
              end
            | inright _ => GT _
            end
          end)
        (fun ys =>
          match ys with
          | nil => EQ _
          | _ => LT _
          end)
        (fun x xs Hx Hxs ys =>
          match ys with
          | nil => GT _
          | y :: ys =>
            match Hx y with
            | LT Hxy => LT _
            | EQ Hxy =>
              match Hxs ys with
              | LT Hxsys => LT _
              | EQ Hxsys => EQ _
              | GT Hxsys => GT _
              end
            | GT Hxy => GT _
            end
          end));
        trivial;
        try congruence;
        try (now left);
        try rewrite Hij;
        try (now right; tauto);
          rewrite Hxy.
          now rewrite Hxsys.

          right; tauto.
    Defined.
  End MiniOrdered.

  Module Ordered <: OrderedType := MOT_to_OT MiniOrdered.

  Module FMap := Map Ordered.
  Module FSet := FSetAVL.Make Ordered.

  (** Add a new element to a map doing the union with the previous ones *)
  Definition addUnion (k: t) (s: FSet.t) (m: FMap.t FSet.t): FMap.t FSet.t :=
    let s :=
      match FMap.find k m with
      | None => s
      | Some s' => FSet.union s s'
      end in
    FMap.add k s m.

  Definition subTermsWithPreds (index: t): FMap.t FSet.t :=
    let fix aux index preds :=
      match index with
      | Make _ indexes =>
        addUnion index preds (fold_left (fun m index' =>
          FMap.fold addUnion m (aux index' (FSet.add index FSet.empty)))
          indexes (FMap.empty _))
      end in
    aux index FSet.empty.

  Definition addPreds (preds1 preds2: FMap.t FSet.t): FMap.t FSet.t :=
    FMap.fold addUnion preds1 preds2.

  (** The map of predecessors of a list of indexes *)
  Definition Preds (indexes: list t): FMap.t FSet.t :=
    fold_left (fun preds index =>
      addPreds preds (subTermsWithPreds index))
      indexes (FMap.empty _).

  Module Tests.
    Definition index1: t :=
      Make 1 [
        Make 2 nil;
        Make 3 nil].
    Definition index2: t :=
      Make 1 [
        Make 2 nil].

    Definition preds1 := subTermsWithPreds index1.
    Definition preds2 := subTermsWithPreds index2.

    Compute preds1.
    Compute preds2.
    Compute addPreds preds1 preds2.

    Compute FMap.cardinal preds1.
    Check eq_refl: FMap.cardinal preds1 = 3.
    Check eq_refl:
      FMap.equal FSet.equal (addPreds preds1 preds1) preds1 = true.
  End Tests.
End Index.

(** Functions to compute the meaning of an index given a list of values *)
Module Values.
  Definition t (T: Type) := list (Value.t T).

  (** The value at an integer index *)
  Definition Nth (T: Type) (values: t T) (n: nat): option (Value.t T) :=
    nth_error values n.

  Definition nthIndexAux (T: Type) (values: t T) :=
    Index.DoubleRecT
      (fun _ => option T)
      (fun _ => option (list T))
      (fun i xs ovs =>
        Option.Bind (Nth values i) (fun value =>
        let (arity, v) := value in
        Option.Bind ovs (fun vs =>
        match eq_nat_dec arity (length vs) with
        | right _ => None
        | left _ => Some (v vs)
        end
        )))
      (Some nil)
      (fun x xs v vs =>
        Option.Bind v (fun v =>
        Option.Bind vs (fun vs =>
        Some (v :: vs)))).

  (** The value at an index *)
  Definition NthIndex (T: Type) (values: t T) (x: Index.t): option T :=
    fst (nthIndexAux values) x.

  (* The values at a list of indexes *)
  Definition NthIndexes (T: Type) (values: t T) (xs: list Index.t)
    : option (list T) :=
    snd (nthIndexAux values) xs.

  (** If two indexes represent the same value *)
  Definition AreEqual (T: Type) (values: t T) (x y: Index.t): Prop :=
    NthIndex values x = NthIndex values y.

  (** If two lists of indexes represent the same values *)
  Definition AreEqualList (T: Type) (values: t T)
    (xs ys: list Index.t): Prop :=
    NthIndexes values xs = NthIndexes values ys.

  (** An equivalent definition of [AreEqualList], easier to prove recursively *)
  Fixpoint AreEqualList' (T: Type) (values: t T)
    (xs ys: list Index.t): Prop :=
    match (xs, ys) with
    | (nil, nil) => True
    | (x :: xs', y :: ys') =>
      AreEqual values x y /\ AreEqualList' values xs' ys'
    | _ => False
    end.

  (** [AreEqualList'] implies [AreEqualList] *)
  Lemma AreEqualList'ImpliesAreEqualList (T: Type) (values: t T):
    forall (xs ys: list Index.t),
    AreEqualList' values xs ys -> AreEqualList values xs ys.
    induction xs as [| x xs]; destruct ys as [| y ys]; simpl; intro H'xsys;
      try apply eq_refl; try tauto.
    destruct H'xsys as [Hxy H'xsys].
    assert (Hxsys := IHxs _ H'xsys); clear H'xsys IHxs.
    destruct x as [i xs']; destruct y as [j ys'].
    revert Hxy Hxsys.
    unfold AreEqual, NthIndex, AreEqualList, NthIndexes; simpl.
    (Option.CaseBind value_i Hvalue_i; simpl; [
      destruct value_i as [arity_i value_i];
      Option.CaseBind vxs' Hvxs'; simpl;
      [destruct (eq_nat_dec arity_i (Datatypes.length vxs')) as [Hai |]; simpl
        |] |]);
    (Option.CaseBind value_j Hvalue_j; simpl; [
      destruct value_j as [arity_j value_j];
      Option.CaseBind vys' Hvys'; simpl;
      [destruct (eq_nat_dec arity_j (Datatypes.length vys')) as [Haj |]; simpl
        |] |]); trivial; try (
      (Option.CaseBind vxs Hvxs; simpl);
      (Option.CaseBind vys Hvys; simpl); trivial); congruence.
  Defined.

  Ltac simplVs values xs vxs Hvxs Hvxs' :=
    try (
      assert (Hvxs': NthIndexes values xs = Some vxs);
      [now trivial | clear Hvxs]);
    try (
      assert (Hvxs': NthIndexes values xs = None);
      [now trivial | clear Hvxs]).

  (** If all the sub-terms are equal then the main values are equal *)
  Lemma CongruenceRule: forall (T: Type) (values: t T)
    (i: nat) (xs ys: list Index.t), AreEqualList values xs ys ->
    AreEqual values (Index.Make i xs) (Index.Make i ys).
    intros T values i xs ys Hxsys.
    unfold AreEqual, NthIndex; simpl.
    (Option.CaseBind value_i Hvalue_i; simpl;
      [destruct value_i as [arity_i vi];
      Option.CaseBind vxs Hvxs; simpl;
        [destruct (eq_nat_dec arity_i (Datatypes.length vxs)) as [Hai |]; simpl
        |] |]); trivial;
    (Option.CaseBind vys Hvys; simpl;
        [destruct (eq_nat_dec arity_i (Datatypes.length vys)) as [Haj |]; simpl
        |]); trivial; [
    intros Hvys Hvxs Hi |
    intros Hvys Hvxs Hi |
    intros Hvxs Hi |
    intros Hvys Hvxs Hi |
    intros Hvys Hi ];
    try simplVs values xs vxs Hvxs Hvxs';
    try simplVs values ys vys Hvys Hvys';
    congruence.
  Defined.

  Module Tests.
    Definition values: t nat :=
      Value.Make 0 (fun _ => 12) ::
      Value.Make 0 (fun _ => 23) ::
      Value.Make 2 (fun v =>
        match v with
        | x1 ::  x2 :: nil => x1 + x2
        | _ => 0
        end) ::
      nil.

    Definition index: Index.t :=
      Index.Make 2 (
        Index.Make 0 nil ::
        Index.Make 1 nil ::
        nil).

    Check eq_refl: NthIndex values index = Some 35.
    Check eq_refl: AreEqual values index index.
  End Tests.
End Values.

(** The user gives equality proofs as hypothesis for congruence-closure *)
Module EqProof.
  (** Two indexes and the proof of their equality *)
  Record t (T: Type) (values: Values.t T) := Make {
    i: Index.t;
    j: Index.t;
    H: Values.AreEqual values i j}.
End EqProof.

(** Global parameters to congruence-closure *)
Module Type Parameters.
  Parameter T: Type.
  Parameter Values: Values.t T.
End Parameters.

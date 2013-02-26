(** Congruence closure *)
Require Import Arith.
Require Import Omega.
Require Import String.
Require Import List.
Require Import OrderedType.
Require Import FSetAVL.
Require Import Coqbottom.
Require Import Coqbottom.Map.
Require Import Coqbottom.DataStructures.

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
  Compute Eval 10 ((0, 1) :: (0, 0) :: (2, 9) :: (1, 4) :: (4, 1) :: nil) 2.
End UnionFind.

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

(** The congruence-closure algorithm *)
Module CongruenceClosure (P: Parameters).
  Definition T: Type := EqProof.t P.Values.
  
  Definition Sig: Sig.t := Sig.Make nil
    (Index.FMap.t T :: (bool: Type) :: nil).
  
  Definition Hash := Ref.t Sig (Index.FMap.t T).
  Definition M := M Sig.
  
  Definition read (hash: Hash) (key: Index.t): M T :=
    let! map := !hash in
    match Index.FMap.find key map with
    | None => error "Hash read: not found"
    | Some v => ret v
    end.
  
  Definition write (hash: Hash) (key: Index.t) (value: T): M unit :=
    let! map := !hash in
    match Index.FMap.find key map with
    | None => error "Hash write: not found"
    | Some _ => hash :=! Index.FMap.add key value map
    end.
  
  Definition do (map: Index.FMap.t (M unit)): M (Index.FMap.t unit) :=
    Index.FMap.fold (fun k x map' =>
      let! x := x in
      let! map' := map' in
      ret (Index.FMap.add k x map'))
      map (ret (Index.FMap.empty _)).
  
  Definition iter (hash: Hash) (f: Index.t -> T -> M unit): M unit :=
    let! map := !hash in
    do! do (Index.FMap.mapi f map) in
    ret tt.
  
  Definition Find (hash: Hash) (index: Index.t)
    : M {index': Index.t | Values.AreEqual P.Values index index'}.
    refine (
      dependent_fix (fun i => {j: Index.t | Values.AreEqual P.Values i j})
        (fun f i =>
          let! eq_proof := read hash i in
          let (i', j, Hij) := eq_proof in
          match Index.Ordered.eq_dec i i' with
            | left Pii' => _
            | right Pii' => error "Find: i <> i' unexpected" % string
          end)
        index).
    refine (
      match Index.Ordered.eq_dec i j with
        | left _ => ret (exist _ j _)
        | right _ =>
          let! r := f j in
          let (k, Hjk) := r in
          do! write hash i (EqProof.Make (i := i) (j := k) _) in
          ret (exist _ k _)
      end);
      congruence.
  Defined.
  
  (** Do the union and return [true] if the values were in different sets *)
  Definition Merge (hash: Hash) (Hij: T): M bool.
    refine (
      let (i, j, Hij) := Hij in
      let! Pii' := Find hash i in
      let! Pjj' := Find hash j in
      let (i', Hii') := Pii' in
      let (j', Hjj') := Pjj' in
      match Index.Ordered.eq_dec i' j' with
      | left _ => ret false
      | right _ =>
        do! write hash i' (EqProof.Make (i := i') (j := j') _) in
        ret true
      end).
    congruence.
  Defined.
  
  (** The equality proof of two values if they are equivalent *)
  Definition AreEquiv (hash: Hash) (i j: Index.t)
    : M (option (Values.AreEqual P.Values i j)).
    refine (
      let! Pii' := Find hash i in
      let! Pjj' := Find hash j in
      let (i', Hii') := Pii' in
      let (j', Hjj') := Pjj' in
      match Index.Ordered.eq_dec i' j' with
      | left Hi'j' => ret (Some _)
      | right _ => ret None
      end).
    congruence.
  Defined.
  
  Fixpoint areCongruentAux (xs ys: list Index.t)
    (f: forall (x y: Index.t), M (option (Values.AreEqual P.Values x y)))
    {struct xs}
    : M (option (Values.AreEqualList' P.Values xs ys)).
    destruct xs as [| x xs]; destruct ys as [| y ys];
      [exact (ret (Some I)) | exact (ret None) |
      exact (ret None) | ]; simpl.
    refine (
      let! Pxy := f x y in
      let! Pxsys := areCongruentAux xs ys f in
      match (Pxy, Pxsys) with
      | (Some _, Some _) => ret (Some _)
      | _ => ret None
      end); tauto.
  Defined.
  
  (** The equality proof of two values if they are congruent *)
  Definition AreCongruent (hash: Hash)
    : forall (ij: Index.t * Index.t),
      M (option (Values.AreEqual P.Values (fst ij) (snd ij))).
    refine (dependent_fix
      (fun xy => option (Values.AreEqual P.Values (fst xy) (snd xy)))
      _); intros f xy.
    destruct xy as [x y].
    refine (
      let! OHxy := AreEquiv hash x y in
      match OHxy with
      | Some _ => ret OHxy
      | None => _
      end); clear OHxy.
    destruct x as [i xs]; destruct y as [j ys]; simpl.
    refine (
      match eq_nat_dec i j with
      | left Hij =>
        let! OHxsys := areCongruentAux xs ys (fun x y => f (x, y)) in
        match OHxsys with
        | None => ret None
        | Some Hxsys => ret (Some _)
        end
      | _ => ret None
      end).
    rewrite Hij.
    apply Values.CongruenceRule.
    now apply Values.AreEqualList'ImpliesAreEqualList.
  Defined.
  
  (** Merge two equal values and merge the new congruent terms *)
  Definition RecurseMerge (hash: Hash) (get_preds: Index.t -> M Index.FSet.t)
    (Pij: T): M bool :=
    fix_ (fun recurse_merge Pij =>
      let! b := Merge hash Pij in
      if b then
        let (i, j, _) := Pij in
        let! ps := get_preds i in
        let! qs := get_preds j in
        do!
          Index.FSet.fold (fun p next =>
            do! next in
            Index.FSet.fold (fun q next =>
              do! next in
              let! P := AreCongruent hash (p, q) in
              match P with
              | Some P =>
                do! recurse_merge (EqProof.Make P) in
                ret tt
              | None => ret tt
              end)
              qs (ret tt))
            ps (ret tt) in
        ret true
      else
        ret false)
      Pij.
  
  (** Do a merge in [hash] if they are still some congruent values *)
  Definition TryMergeCongruent (hash: Hash): M bool :=
    let! r := tmp_ref Sig 1 false in
    do!
      iter hash (fun x _ =>
      iter hash (fun y _ =>
        let! OPxy := AreCongruent hash (x, y) in
        match OPxy with
        | Some Pxy =>
          let! b := Merge hash (EqProof.Make Pxy) in
          if b
          then r :=! true
          else ret tt
        | None => ret tt
       end)) in
     !r.
  
  (** Merge congruent values until a fixpoint is reached (slow version) *)
  Definition CongruenceClosureNaive  (eq_proofs: list T)
    (other_indexes: list Index.t): M Hash :=
    let preds :=
      Index.Preds (other_indexes ++ flat_map (fun (P: T) =>
        let (i, j, _) := P in
        i :: j :: nil) eq_proofs) in
    let! hash := tmp_ref Sig 0 (Index.FMap.mapi (fun i _ =>
      EqProof.Make (i := i) (j := i) eq_refl) preds) in
    do! List.do (List.map (Merge hash) eq_proofs) in
    let! continue := tmp_ref Sig 1 true in
    do! while (fun _ => !continue) (fun _ =>
      let! b := TryMergeCongruent hash in
      continue :=! b) in
    ret hash.
  
  (** Generate the congruent relation given a list of equalities and
      other involved terms *)
  Definition CongruenceClosure (eq_proofs: list T) (other_indexes: list Index.t)
    : M Hash :=
    let preds :=
      Index.Preds (other_indexes ++ flat_map (fun (P: T) =>
        let (i, j, _) := P in
        i :: j :: nil) eq_proofs) in
    let get_preds (i: Index.t): M Index.FSet.t :=
      match Index.FMap.find i preds with
      | Some s => ret s
      | None => error "Invalid index in preds" % string
      end in
    let! hash := tmp_ref Sig 0 (Index.FMap.mapi (fun i _ =>
      EqProof.Make (i := i) (j := i) eq_refl) preds) in
    do! List.do (List.map (RecurseMerge hash get_preds) eq_proofs) in
    ret hash.
  
  (** Compute the equality proof of two terms with congruence-closure *)
  Definition ProveEqual (eq_proofs: list T) (i j: Index.t)
    : M (Values.AreEqual P.Values i j).
    refine (
      let! hash := CongruenceClosure eq_proofs (i :: j :: nil) in
      let! Pii' := Find hash i in
      let! Pjj' := Find hash j in
      let (i', Hii') := Pii' in
      let (j', Hjj') := Pjj' in
      match Index.Ordered.eq_dec i' j' with
      | left Hi'j' => ret _
      | right _ => error "Equality proof not found" % string
      end).
    rewrite Hi'j' in Hii'.
    apply (eq_trans Hii').
    now apply eq_sym.
  Defined.
End CongruenceClosure.

(** Example with only constants *)
Module ExampleNoFun.
  Module P <: Parameters.
    Definition T := nat.
    Definition Values :=
      let values := 3 :: 5 :: 5 :: 6 :: 3 :: 0 :: 5 :: nil in
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
  
  Module CC := CongruenceClosure P.
  Import CC.
  
  Definition a := Index.Make 0 nil.
  Definition b := Index.Make 1 nil.
  Definition fa := Index.Make 2 (a :: nil).
  Definition gab := Index.Make 3 (a :: b :: nil).
  Definition fgba := Index.Make 2 (Index.Make 3 (b :: a :: nil) :: nil).
  Definition gbfa := Index.Make 3 (b :: fa :: nil).
  Definition ffa := Index.Make 2 (fa :: nil).
  
  Check eq_refl: Values.NthIndex P.Values a = Some 3.
  Check eq_refl: Values.NthIndex P.Values fa = Some 3.
  Check eq_refl: Values.NthIndex P.Values ffa = Some 3.
  Check eq_refl: Values.NthIndex P.Values fgba = Some 3.
  
  Definition eq_proofs: list T.
    refine (
      EqProof.Make (i := a) (j := fa) _ ::
      EqProof.Make (i := gab) (j := fgba) _ ::
      EqProof.Make (i := gbfa) (j := ffa) _ ::
      EqProof.Make (i := gab) (j := a) _ ::
      nil); now unfold Values.AreEqual.
  Defined.
  
  Definition Equal (i j: Index.t) :=
    proof_by_reflection (ProveEqual eq_proofs i j) (Prophecy.of_nat Sig 100).
  
  Time Check Equal a a eq_refl.
  Time Check Equal a fa eq_refl.
  Time Check Equal a ffa eq_refl.
  Time Fail Check Equal a b eq_refl.
  Time Check Equal gab a eq_refl.
  
  Lemma Eq1: Values.AreEqual P.Values a ffa.
    now apply (proof_by_reflection (ProveEqual eq_proofs a ffa)
      (Prophecy.of_nat Sig 100)).
  Defined.
  
  Lemma Eq2: Values.AreEqual P.Values gab a.
    now apply (proof_by_reflection (ProveEqual eq_proofs gab a)
      (Prophecy.of_nat Sig 100)).
  Defined.
End ExampleBig.

Module Certificate (P: Parameters).
  Require Import Coqbottom.Reifiable.
  
  Inductive t :=
  | proof: nat -> t
  | sym: t -> t
  | trans: t -> t -> t
  | congruence: nat -> list t -> t.
  
  Fixpoint build_eq_proof_by_congruence_aux (eq_proofs: list (EqProof.t P.Values))
    : let xs := List.map (fun p: EqProof.t _ => let (x, _, _) := p in x) eq_proofs in
      let ys := List.map (fun p: EqProof.t _ => let (_, y, _) := p in y) eq_proofs in
      Values.AreEqualList' P.Values xs ys.
    destruct eq_proofs as [| p ps]; simpl.
      exact I.
      
      split.
        destruct p as [x y P].
        exact P.
        
        apply (build_eq_proof_by_congruence_aux ps).
  Qed.
  
  Definition build_eq_proof_by_congruence
    (f: nat) (eq_proofs: list (EqProof.t P.Values))
    : EqProof.t P.Values.
    refine (
      let xs := List.map (fun p: EqProof.t _ => let (x, _, _) := p in x) eq_proofs in
      let ys := List.map (fun p: EqProof.t _ => let (_, y, _) := p in y) eq_proofs in
      EqProof.Make (i := Index.Make f xs) (j := Index.Make f ys) _).
      apply Values.CongruenceRule.
      apply Values.AreEqualList'ImpliesAreEqualList.
      apply build_eq_proof_by_congruence_aux.
  Defined.
  
  Definition to_proof (eq_proofs: list (EqProof.t P.Values))
    : t -> M Sig.empty (EqProof.t P.Values).
    refine (fix_ (fun rec c =>
      match c with
      | proof k => extract_some (nth_error eq_proofs k)
      | sym c' =>
        let! proof := rec c' in
        let (j, i, P) := proof in
        ret (EqProof.Make (i := j) (j := i) _)
      | trans c1 c2 =>
        let! proof1 := rec c1 in
        let! proof2 := rec c2 in
        let (i, k, P1) := proof1 in
        let (k', j, P2) := proof2 in
        match Index.Ordered.eq_dec k k' with
        | left Pkk' => ret (EqProof.Make (i := i) (j := j) _)
        | right _ => error "Expected k = k'."
        end
      | congruence f cs =>
        let! proofs := List.do (List.map rec cs) in
        ret (build_eq_proof_by_congruence f proofs)
      end));
    congruence.
  Defined.
  
  Import SExpr.
  
  Definition reifiable: Reifiable.t Certificate.t :=
    Reifiable.New
      (fix export c :=
        let fix export_list cs :=
          match cs with
          | nil => I
          | c :: cs' => B (export c) (export_list cs')
          end in
        match c with
        | proof k => B I (Reifiable.Export Reifiable.Nat k)
        | sym c' => B (B I I) (export c')
        | trans c1 c2 => B (B I (B I I)) (B (export c1) (export c2))
        | congruence f cs =>
          B (B (B I I) I) (B (Reifiable.Export Reifiable.Nat f) (export_list cs))
        end)
      (fix import s :=
        let fix import_list s :=
          match s with
          | I => nil
          | B s1 s2 => import s1 :: import_list s2
          end in
        match s with
        | B I s' => proof (Reifiable.Import Reifiable.Nat s')
        | B (B I I) s' => sym (import s')
        | B (B I (B I I)) (B s1 s2) => trans (import s1) (import s2)
        | B _ (B s1 s2) => congruence (Reifiable.Import Reifiable.Nat s1) (import_list s2)
        | _ => proof O
        end).
End Certificate.

Module CongruenceClosureByCertificate (P: Parameters).
  Module Certificate := Certificate P.
  Definition T: Type := Index.t * Certificate.t.
  
  (*Definition Sig: Sig.t := Sig.Make [] [].
    (Index.FMap.t T :: (bool: Type) :: nil).
  
  Definition Hash := Ref.t Sig (Index.FMap.t T).
  Definition M := M Sig.
  
  Definition read (hash: Hash) (key: Index.t): M T :=
    let! map := !hash in
    match Index.FMap.find key map with
    | None => error "Hash read: not found"
    | Some v => ret v
    end.
  
  Definition write (hash: Hash) (key: Index.t) (value: T): M unit :=
    let! map := !hash in
    match Index.FMap.find key map with
    | None => error "Hash write: not found"
    | Some _ => hash :=! Index.FMap.add key value map
    end.
  
  Definition do (map: Index.FMap.t (M unit)): M (Index.FMap.t unit) :=
    Index.FMap.fold (fun k x map' =>
      let! x := x in
      let! map' := map' in
      ret (Index.FMap.add k x map'))
      map (ret (Index.FMap.empty _)).
  
  Definition iter (hash: Hash) (f: Index.t -> T -> M unit): M unit :=
    let! map := !hash in
    do! do (Index.FMap.mapi f map) in
    ret tt.
  
  Definition Find (hash: Hash) (index: Index.t)
    : M {index': Index.t | Values.AreEqual P.Values index index'}.
    refine (
      dependent_fix (fun i => {j: Index.t | Values.AreEqual P.Values i j})
        (fun f i =>
          let! eq_proof := read hash i in
          let (i', j, Hij) := eq_proof in
          match Index.Ordered.eq_dec i i' with
            | left Pii' => _
            | right Pii' => error "Find: i <> i' unexpected" % string
          end)
        index).
    refine (
      match Index.Ordered.eq_dec i j with
        | left _ => ret (exist _ j _)
        | right _ =>
          let! r := f j in
          let (k, Hjk) := r in
          do! write hash i (EqProof.Make (i := i) (j := k) _) in
          ret (exist _ k _)
      end);
      congruence.
  Defined.
  
  (** Do the union and return [true] if the values were in different sets *)
  Definition Merge (hash: Hash) (Hij: T): M bool.
    refine (
      let (i, j, Hij) := Hij in
      let! Pii' := Find hash i in
      let! Pjj' := Find hash j in
      let (i', Hii') := Pii' in
      let (j', Hjj') := Pjj' in
      match Index.Ordered.eq_dec i' j' with
      | left _ => ret false
      | right _ =>
        do! write hash i' (EqProof.Make (i := i') (j := j') _) in
        ret true
      end).
    congruence.
  Defined.
  
  (** The equality proof of two values if they are equivalent *)
  Definition AreEquiv (hash: Hash) (i j: Index.t)
    : M (option (Values.AreEqual P.Values i j)).
    refine (
      let! Pii' := Find hash i in
      let! Pjj' := Find hash j in
      let (i', Hii') := Pii' in
      let (j', Hjj') := Pjj' in
      match Index.Ordered.eq_dec i' j' with
      | left Hi'j' => ret (Some _)
      | right _ => ret None
      end).
    congruence.
  Defined.
  
  Fixpoint areCongruentAux (xs ys: list Index.t)
    (f: forall (x y: Index.t), M (option (Values.AreEqual P.Values x y)))
    {struct xs}
    : M (option (Values.AreEqualList' P.Values xs ys)).
    destruct xs as [| x xs]; destruct ys as [| y ys];
      [exact (ret (Some I)) | exact (ret None) |
      exact (ret None) | ]; simpl.
    refine (
      let! Pxy := f x y in
      let! Pxsys := areCongruentAux xs ys f in
      match (Pxy, Pxsys) with
      | (Some _, Some _) => ret (Some _)
      | _ => ret None
      end); tauto.
  Defined.
  
  (** The equality proof of two values if they are congruent *)
  Definition AreCongruent (hash: Hash)
    : forall (ij: Index.t * Index.t),
      M (option (Values.AreEqual P.Values (fst ij) (snd ij))).
    refine (dependent_fix
      (fun xy => option (Values.AreEqual P.Values (fst xy) (snd xy)))
      _); intros f xy.
    destruct xy as [x y].
    refine (
      let! OHxy := AreEquiv hash x y in
      match OHxy with
      | Some _ => ret OHxy
      | None => _
      end); clear OHxy.
    destruct x as [i xs]; destruct y as [j ys]; simpl.
    refine (
      match eq_nat_dec i j with
      | left Hij =>
        let! OHxsys := areCongruentAux xs ys (fun x y => f (x, y)) in
        match OHxsys with
        | None => ret None
        | Some Hxsys => ret (Some _)
        end
      | _ => ret None
      end).
    rewrite Hij.
    apply Values.CongruenceRule.
    now apply Values.AreEqualList'ImpliesAreEqualList.
  Defined.
  
  (** Merge two equal values and merge the new congruent terms *)
  Definition RecurseMerge (hash: Hash) (get_preds: Index.t -> M Index.FSet.t)
    (Pij: T): M bool :=
    fix_ (fun recurse_merge Pij =>
      let! b := Merge hash Pij in
      if b then
        let (i, j, _) := Pij in
        let! ps := get_preds i in
        let! qs := get_preds j in
        do!
          Index.FSet.fold (fun p next =>
            do! next in
            Index.FSet.fold (fun q next =>
              do! next in
              let! P := AreCongruent hash (p, q) in
              match P with
              | Some P =>
                do! recurse_merge (EqProof.Make P) in
                ret tt
              | None => ret tt
              end)
              qs (ret tt))
            ps (ret tt) in
        ret true
      else
        ret false)
      Pij.
  
  (** Do a merge in [hash] if they are still some congruent values *)
  Definition TryMergeCongruent (hash: Hash): M bool :=
    let! r := tmp_ref Sig 1 false in
    do!
      iter hash (fun x _ =>
      iter hash (fun y _ =>
        let! OPxy := AreCongruent hash (x, y) in
        match OPxy with
        | Some Pxy =>
          let! b := Merge hash (EqProof.Make Pxy) in
          if b
          then r :=! true
          else ret tt
        | None => ret tt
       end)) in
     !r.
  
  (** Merge congruent values until a fixpoint is reached (slow version) *)
  Definition CongruenceClosureNaive  (eq_proofs: list T)
    (other_indexes: list Index.t): M Hash :=
    let preds :=
      Index.Preds (other_indexes ++ flat_map (fun (P: T) =>
        let (i, j, _) := P in
        i :: j :: nil) eq_proofs) in
    let! hash := tmp_ref Sig 0 (Index.FMap.mapi (fun i _ =>
      EqProof.Make (i := i) (j := i) eq_refl) preds) in
    do! List.do (List.map (Merge hash) eq_proofs) in
    let! continue := tmp_ref Sig 1 true in
    do! while (fun _ => !continue) (fun _ =>
      let! b := TryMergeCongruent hash in
      continue :=! b) in
    ret hash.
  
  (** Generate the congruent relation given a list of equalities and 
      other involved terms *)
  Definition CongruenceClosure (eq_proofs: list T) (other_indexes: list Index.t)
    : M Hash :=
    let preds :=
      Index.Preds (other_indexes ++ flat_map (fun (P: T) =>
        let (i, j, _) := P in
        i :: j :: nil) eq_proofs) in
    let get_preds (i: Index.t): M Index.FSet.t :=
      match Index.FMap.find i preds with
      | Some s => ret s
      | None => error "Invalid index in preds" % string
      end in
    let! hash := tmp_ref Sig 0 (Index.FMap.mapi (fun i _ =>
      EqProof.Make (i := i) (j := i) eq_refl) preds) in
    do! List.do (List.map (RecurseMerge hash get_preds) eq_proofs) in
    ret hash.
  
  (** Compute the equality proof of two terms with congruence-closure *)
  Definition ProveEqual (eq_proofs: list T) (i j: Index.t)
    : M (Values.AreEqual P.Values i j).
    refine (
      let! hash := CongruenceClosure eq_proofs (i :: j :: nil) in
      let! Pii' := Find hash i in
      let! Pjj' := Find hash j in
      let (i', Hii') := Pii' in
      let (j', Hjj') := Pjj' in
      match Index.Ordered.eq_dec i' j' with
      | left Hi'j' => ret _
      | right _ => error "Equality proof not found" % string
      end).
    rewrite Hi'j' in Hii'.
    apply (eq_trans Hii').
    now apply eq_sym.
  Defined.*)
End CongruenceClosureByCertificate.
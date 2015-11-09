(** Congruence closure *)
Require Import Arith.Peano_dec.
Require Import List.
Require Import Cybele.Cybele.
Require Import Cybele.Map.
Require Import Cybele.DataStructures.
Require Import Definitions.

Set Implicit Arguments.
Set Transparent Obligation.
Import Monad ListNotations.

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
            | right Pii' => error "Find: i <> i' unexpected"
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
      | None => error "Invalid index in preds"
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
      | right _ => error "Equality proof not found"
      end).
    rewrite Hi'j' in Hii'.
    apply (eq_trans Hii').
    now apply eq_sym.
  Defined.
End CongruenceClosure.

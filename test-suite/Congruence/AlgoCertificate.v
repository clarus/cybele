(** Congruence closure *)
Require Import Arith.Peano_dec.
Require Import List.
Require Import Coqbottom.
Require Import Coqbottom.Map.
Require Import Coqbottom.DataStructures.
Require Import Definitions.

Set Implicit Arguments.
Set Transparent Obligation.
Import Monad ListNotations.

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
  Require Import Coqbottom.Reifiable.
  
  Module Certificate := Certificate P.
  Definition T: Type := Index.t * Certificate.t.
  
  (* Universe inconsistency *)
  (*Module ReifiableIndexMap := Reifiable.Map Index.FMap.
  
  Definition Sig: Sig.t := Sig.Make [] [].
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
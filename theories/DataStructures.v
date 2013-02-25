Require Import Arith.Compare_dec.
Require Import List.
Require Import Map.
Require Import Monad.

Set Implicit Arguments.

Module List.
  Import Monad.
  
  (** List map with index *)
  Definition mapi (A B: Type) (f: A -> nat -> B) (l: list A): list B :=
    let fix aux (l: list A) (i: nat): list B :=
      match l with
      | nil => nil
      | x :: l' => (f x i) :: (aux l' (S i))
      end
    in
      aux l 0.
  
  (** Evaluate each action in the list from left to right
      and collect the results. *)
  Definition do (sig: Sig.t) (T: Type) (l: list (M sig T))
    : M sig (list T) :=
    fold_right (fun x l' =>
      let! x := x in
      let! l' := l' in
      ret (x :: l'))
      (ret nil) l.
  
  (** Apply an effectful function to each element of a list. *)
  Definition iter (sig: Sig.t) (T: Type)
    (f: T -> M sig unit) (l: list T): M sig unit :=
    do! do (map f l) in
    ret tt.
End List.

(** A data structure for arrays implemented in the monad. *)
(* FIXME: Implement it using a more efficient data structure. *)
Module Array.
  Import Monad.
  
  Definition internal_t (T: Type): Type :=
    list T.
  
  Definition t (sig: Sig.t) (T: Type): Type :=
    Ref.t sig (internal_t T).
  
  (** Read a value. *)
  Definition read (sig: Sig.t) (T: Type) (array: t sig T) (index: nat)
    : M sig T :=
    let! l := !array in
    match nth_error l index with
    | Some v => ret v
    | None => error "Invalid array read"
    end.
  
  (** Write a value. *)
  Definition write (sig: Sig.t) (T: Type) (array: t sig T) (index: nat) (v: T)
    : M sig unit :=
    let! l := !array in
    match lt_dec index (length l) with
    | left _ => array :=! (firstn index l ++ (v :: nil) ++ skipn (S index) l)
    | right _ => error "Invalid array write"
    end.
  
  (** Modify an array applying a function to each element. *)
  Definition map (sig: Sig.t) (T: Type) (array: t sig T)
    (f: T -> nat -> M sig T): M sig unit :=
    let! l := !array in
    let! l := List.do (List.mapi f l) in
    array :=! l.
  
  (** Convert to a persistent list. *)
  Definition to_list (sig: Sig.t) (T: Type) (array: t sig T)
    : M sig (list T) :=
    !array.
End Array.

(** An mutable associative data structure. *)
Module Hash (Map: IMap).
  Import Monad.
  
  Definition internal_t (T: Type): Type := Map.t T.
  
  Definition t (sig: Sig.t) (T: Type) := Ref.t sig (internal_t T).
  
  (** Evaluate each action in the hash table. *)
  Definition do (sig: Sig.t) (T: Type) (map: internal_t (M sig T))
    : M sig (internal_t T) :=
    Map.fold (fun k x map' =>
      let! x := x in
      let! map' := map' in
      ret (Map.add k x map'))
      map (ret (Map.empty _)).
  
  (** Read a value. *)
  Definition read (sig: Sig.t) (T: Type) (hash: t sig T)
    (key: Map.key): M sig T :=
    let! map := !hash in
    match Map.find key map with
    | None => error "Hash read: not found"
    | Some v => ret v
    end.
  
  (** Write a value. *)
  Definition write (sig: Sig.t) (T: Type) (hash: t sig T)
    (key: Map.key) (value: T): M sig unit :=
    let! map := !hash in
    match Map.find key map with
    | None => error "Hash write: not found"
    | Some _ => hash :=! Map.add key value map
    end.
  
  (** Iterate a function over each element. *)
  Definition iter (sig: Sig.t) (T: Type) (hash: t sig T)
    (f: Map.key -> T -> M sig unit): M sig unit :=
    let! map := !hash in
    do! do (Map.mapi f map) in
    ret tt.
  
  (** Convert to a persistent map. *)
  Definition to_map (sig: Sig.t) (T: Type) (hash: t sig T)
    : M sig (Map.t T) :=
    !hash.
End Hash.
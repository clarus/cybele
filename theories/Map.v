(** Different implementations of maps *)
Require Import DecidableType.
Require Import OrderedType.
Require Import Int.
Require Import FMapAVL.
Require Import FMapWeakList.

Set Implicit Arguments.

(** Interface for maps without specification. *)
Module Type IMap.
  Parameter key: Type.
  Parameter t: Type -> Type.
  
  Parameter empty: forall (T: Type), t T.
  Parameter add: forall (T: Type), key -> T -> t T -> t T.
  Parameter remove: forall (T: Type), key -> t T -> t T.
  Parameter fold: forall (T A: Type), (key -> T -> A -> A) -> t T -> A -> A.
  Parameter mapi: forall (T T': Type), (key -> T -> T') -> t T -> t T'.
  Parameter find: forall (T: Type), key -> t T -> option T.
  Parameter cardinal: forall (T: Type), t T -> nat.
  Parameter equal: forall (T: Type), (T -> T -> bool) -> t T -> t T -> bool.
End IMap.

(** Maps implemented using [FMapAVL.Raw]. *)
Module Map (X: OrderedType) <: IMap.
  Module Map := FMapAVL.Raw Z_as_Int X.
  
  Definition key := Map.key.
  Definition t := Map.t.
  
  Definition empty := Map.empty.
  Definition add := Map.add.
  Definition remove := Map.remove.
  Definition fold := Map.fold.
  Definition mapi := Map.mapi.
  Definition find := Map.find.
  Definition cardinal := Map.cardinal.
  Definition equal := Map.equal.
End Map.

(** Maps implemented using [FMapAVL.Make]; for performance tests only, since
    it computes the invariants which are useless here. *)
Module FullMap (X: OrderedType) <: IMap.
  Module Map := FMapAVL.Make X.
  
  Definition key := Map.key.
  Definition t := Map.t.
  
  Definition empty := Map.empty.
  Definition add := Map.add.
  Definition remove := Map.remove.
  Definition fold := Map.fold.
  Definition mapi := Map.mapi.
  Definition find := Map.find.
  Definition cardinal := Map.cardinal.
  Definition equal := Map.equal.
End FullMap.

(** Maps implemented using [FMapWeakList.Raw]. *)
Module ListMap (X : DecidableType) <: IMap.
  Module Map := FMapWeakList.Raw X.
  
  Definition key := Map.key.
  Definition t := Map.t.
  
  Definition empty := Map.empty.
  Definition add := Map.add.
  Definition remove := Map.remove.
  Definition fold := Map.fold.
  Definition mapi := Map.mapi.
  Definition find := Map.find.
  Definition cardinal (T: Type) := length (A := key * T).
  Definition equal := Map.equal.
End ListMap.

(*Module ListMap (X : DecidableType) <: IMap.
  Require Import List.
  Import ListNotations.
  
  Definition key := X.t.
  Definition t (T: Type) := list (key * T).
  
  Definition empty T := nil (A := T).
  
  Fixpoint add (T: Type) (k: key) (x: T) (m: t T): t T :=
    match m with
    | nil => (k, x) :: nil
    | (k', x') :: m' =>
      if X.eq_dec k k'
      then (k, x) :: m'
      else (k', x') :: add k x m'
    end.
  
  Fixpoint remove (T: Type) (k: key) (x: T) (m: t T): t T :=
    match m with
    | nil => nil
    | (k', x') :: m' =>
      if X.eq_dec k k'
      then m'
      else (k', x') :: remove k x m'
    end.
  
  Fixpoint fold (T A: Type) (f: key -> T -> A -> A) (m: t T) (r: A): A :=
    match m with
    | nil => r
    | (k, x) :: m' => fold f m' (f k x r)
    end.
  
  Definition mapi (T T': Type) (f: key -> T -> T') (m: t T): t T' :=
    map (fun kx => (fst kx, f (fst kx) (snd kx))) m.
  
  Parameter find (T: Type) (k: key) (m: t T): option T :=
    match m with
    | nil => None
    | (k', x) :: m' =>
      if X.eq_dec
  Parameter cardinal: forall (T: Type), t T -> nat.
  Parameter equal: forall (T: Type), (T -> T -> bool) -> t T -> t T -> bool.
End ListMap.*)
(** Memoization is used to pre-compute complex results in OCaml
    and save time in Coq. Several mechanisms are available. *)
Require Import FMapInterface.
Require Import Monad.

Set Implicit Arguments.

(** A trace register a list of results evaluated by OCaml. It can be played-back
    in Coq to retrieve these results. *)
(* FIXME: reverse the trace to play it back! *)
Module Trace.
  Import Monad.
  
  Definition t (sig: Sig.t) (T: Type) := Ref.t sig (list T).
  
  (** Add a new result to the trace. *)
  Definition push (sig: Sig.t) (T: Type) (trace: t sig T) (x: T)
    : M sig unit :=
    let! l := !trace in
    trace :=! x :: l.
  
  (** Get a new result from the trace. *)
  Definition pop (sig: Sig.t) (T: Type) (trace: t sig T)
    : M sig T :=
    let! l := !trace in
    match l with
    | nil => error "Unable to pop from an empty trace"
    | cons x l' =>
      do! trace :=! l' in
      ret x
    end.
  
  (** Evaluate an expression in OCaml and just read the pre-computed result
      in Coq. *)
  Definition eval (sig: Sig.t) (T: Type) (trace: t sig T)
    (f: unit -> M sig T): M sig T :=
    select
      (fun _ => pop trace)
      (fun _ =>
        let! r := f tt in
        do! push trace r in
        ret r).
End Trace.

(** Memoization of functions in the input memory. *)
Module InputMemo (Map: S).
  Import Monad.
  
  Definition input: Type := Map.key.
  
  Definition internal_t (output: Type) := Map.t output.
  Definition t (sig: Sig.t) (output: Type) := Ref.t sig (internal_t output).
  
  (** Memoize a function computing the map from its inputs to its ouputs.
      Generate this result in OCaml and use it Coq. *)
  Definition memoize (sig: Sig.t) (output: Type) (memo: t sig output)
    (f: input -> M sig output) (x: input): M sig output :=
    select
      (fun _ =>
        let! map := !memo in
        match Map.find x map with
        | Some y => ret y
        | None => error "Result not memoized"
        end)
      (fun _ =>
        let! y := f x in
        let! map := !memo in
        do! memo :=! Map.add x y map in
        ret y).
  
  Program Definition lmemoize
    (sig: Sig.t) (n : nat) (output: Type)
    (H: Sig.nth_input_type sig n = (internal_t output)) (f: input -> M sig output)
    : M sig (input -> M sig output) :=
    let memo : t sig output := ▹ (input_ref sig n (▹ (Map.empty output))) in
    ret
      (fun x =>
         select
           (fun _ =>
              let! map := !memo in
                match Map.find x map with
                    | Some y => ret y
                    | None => error "Result not memoized"
            end)
           (fun _ =>
              let! y := f x in
                let! map := !memo in
                  do! memo :=! Map.add x y map in
              ret y)
      ).
  Next Obligation.
  Proof.
    rewrite H in x. assumption.
  Defined.
  Next Obligation.
  Proof.
    rewrite H. assumption.
  Defined.
End InputMemo.

(** Memoization of functions in the temporary memory. More flexible
    since it does not require reification from OCaml, but less efficient. *)
Module TmpMemo (Map: S).
  Import Monad.
  
  Definition input: Type := Map.key.
  
  Definition t_internal (output: Type) := Map.t output.
  Definition t (sig: Sig.t) (output: Type) := Ref.t sig (t_internal output).
  
  (** Memoize a function computing the map from its inputs to its ouputs. *)
  Definition memoize (sig: Sig.t) (output: Type) (memo: t sig output)
    (f: input -> M sig output) (x: input): M sig output :=
    let! map := !memo in
    match Map.find x map with
    | Some y => ret y
    | None =>
      let! y := f x in
      do! memo :=! Map.add x y map in
      ret y
    end.
End TmpMemo.

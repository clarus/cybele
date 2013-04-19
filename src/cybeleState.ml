(** This module manages the state of the plugin which is used
    as a communication medium between the plugin and the dynamically
    compiled code. *)

open CybeleConstants

type sexpr =
  | I
  | B of sexpr * sexpr

let rec mk_sexpr : sexpr -> Term.constr = function
  | I -> Lazy.force SExpr.i
  | B (r1, r2) -> Term.mkApp (Lazy.force SExpr.b, [| mk_sexpr r1; mk_sexpr r2 |])

let n_steps =
  ref 0

let input_refs : (int, unit -> sexpr) Hashtbl.t =
  Hashtbl.create 17

let reset () =
  n_steps := 0;
  Hashtbl.clear input_refs

let observe_recursive_call () =
  incr n_steps

let register_input_ref (index : int) (getter : unit -> sexpr) =
  Hashtbl.add input_refs index getter

let extract_input_list () : sexpr option list =
  let indexes = List.sort compare (Hashtbl.fold (fun i _ indexes -> i :: indexes) input_refs []) in
  let max_index = match List.rev indexes with [] -> 0 | i :: _ -> i in
  let rec aux (index : int) =
    if index > max_index then
      []
    else
      try Some (Hashtbl.find input_refs index ()) :: aux (index + 1) with
      | Not_found -> None :: aux (index + 1) in
  aux 0

let prophecy signature =
  Term.mkApp (Lazy.force Prophecy.of_sexprs, [|
    signature;
    Init.mk_nat !n_steps;
    Init.mk_list (Term.mkApp (Lazy.force Init.option, [| Lazy.force SExpr.t |]))
      (Init.mk_option (Lazy.force SExpr.t) mk_sexpr) (extract_input_list ()) |])

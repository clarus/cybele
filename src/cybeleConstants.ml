(** This module stores the references to the Coq's namespace. *)

let message = "Cybele"
let lookup  = Coqlib.gen_constant_in_modules message

module SExpr = struct
  let constant = lookup [["Cybele"; "Reifiable"; "SExpr"]]

  let t          = lazy (constant "t")

  let i          = lazy (constant "I")
  let b          = lazy (constant "B")
end

module Prophecy = struct
  let constant = lookup [["Cybele"; "Monad"; "Prophecy"]]

  let of_nat        = lazy (constant "of_nat")
  let of_sexprs     = lazy (constant "of_sexprs")
end

module Monad = struct
  let constant = lookup [["Cybele"; "Monad"; "Monad"]]

  let t                      = lazy (constant "M")

  let proof_by_reflection    = lazy (constant "proof_by_reflection")
  let is_computable          = lazy (constant "is_computable")
end

module Init = struct
  let init_constant = lookup Coqlib.init_modules

  let bool       = lazy (init_constant "bool")
  let nat        = lazy (init_constant "nat")
  let option     = lazy (init_constant "option")

  let eq_refl    = lazy (init_constant "eq_refl")

  let _O         = lazy (init_constant "O")
  let _S         = lazy (init_constant "S")

  let none       = lazy (init_constant "None")
  let some       = lazy (init_constant "Some")

  let _nil       = lazy (init_constant "nil")
  let _cons      = lazy (init_constant "cons")

  let rec mk_nat = function
    | 0 -> Lazy.force _O
    | n -> Term.mkApp (Lazy.force _S, [| mk_nat (pred n) |])

  let mk_option typ (mk : 'a -> Term.constr) : 'a option -> Term.constr = function
    | None -> Term.mkApp (Lazy.force none, [| typ |])
    | Some x -> Term.mkApp (Lazy.force some, [| typ; mk x |])

  let rec mk_list typ (mk : 'a -> Term.constr) : 'a list -> Term.constr = function
    | [] -> Term.mkApp (Lazy.force _nil, [| typ |])
    | x :: xs -> Term.mkApp (Lazy.force _cons, [| typ; mk x; mk_list typ mk xs |])
end

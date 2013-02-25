(** This module manages the state of the plugin which is used
    as a communication medium between the plugin and the dynamically
    compiled code.*)

type sexpr =
  | I
  | B of sexpr * sexpr

(** Reset the state of the plugin. *)
val reset : unit -> unit

(** Increment the number of observed recursive calls. *)
val observe_recursive_call : unit -> unit

(** Register an input reference *)
val register_input_ref : int -> (unit -> sexpr) -> unit

(** Exhibit the prophecy hidden in the state of Coqbottom. *)
val prophecy : Term.constr -> Term.constr

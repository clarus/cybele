(** This module implements the dynamic compilation process. *)

(** [compile_and_run_oracle c] compiles and executes the extraction of
    [c]. The communication between the compiled code and the plugin is
    implemented by the module {!CoqbottomState}. *)
val compile_and_run_oracle : Term.constr -> unit

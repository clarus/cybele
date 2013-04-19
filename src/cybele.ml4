open Tacmach
open Entries

open CybeleConstants

(** [check_monadic_computation c] checks that [c] has type [Monad.t s t]
    and returns [s] and [t]. Otherwise an error is raised. *)
let check_monadic_computation c env =
  (** Compute c's type. *)
  let cty = Tacmach.pf_type_of env c in
  (** Check that it is a monadic computation and extract on which
      signature the monad works and what is the type of the returned
      value. *)
  let (head, args) = Term.decompose_app cty in
  if not (Term.eq_constr head (Lazy.force Monad.t)) then
    Errors.error "Cybele: The coq tactic must be applied to a monadic term.";
  match args with
    | [ s; t ] -> (s, t)
    | _ -> assert false (** By [c] being well-typed. *)

(** [monadic_proof_by_reflection s t c p] constructs the term:
    [ProofByReflection (IsComputable c p) c p] *)
let monadic_proof_by_reflection signature rtype c prophecy =
  Term.mkApp
    (Lazy.force Monad.proof_by_reflection, [|
      signature; rtype; c; prophecy;
      Term.mkApp (Lazy.force Init.eq_refl, [|
	Lazy.force Init.bool;
	Term.mkApp (Lazy.force Monad.is_computable, [|
	  signature; rtype; c; prophecy
	|])
      |])
     |])

(** [cybele c env] is the implementation of the tactic. *)
let cybele c env =
(*  Errors.todo "Cybele: starting."; *)
  (** Check tactic precondition. *)
  let signature, rtype = check_monadic_computation c env in
  Errors.todo "Cybele: checked type.";
  (** Reset the state of cybele. *)
  CybeleState.reset ();
  Errors.todo "Cybele: reset state.";
  (** Compile and execute the oracle. *)
  CybeleDynamicCompilation.compile_and_run_oracle c;
  Errors.todo "Cybele: compile and run.";
  (** Compute the prophecy from the state of cybele. *)
  let prophecy = CybeleState.prophecy signature in
  Errors.todo "Cybele: make prophecy.";
  (** Construct the monadic proof-by-reflection. *)
  let proof = monadic_proof_by_reflection signature rtype c prophecy in
  Errors.todo "Cybele: return the proof.";
  (** Apply it. *)
  refine proof env

(** Syntax extension for our tactic. *)
TACTIC EXTEND coq
| [ "coq" constr(c) ] -> [ cybele c ]
END


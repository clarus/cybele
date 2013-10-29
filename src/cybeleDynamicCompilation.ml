(** This module implements the dynamic compilation process. 

    It basically consists in the following steps:

    (i) use the extraction mechanism of Coq to produce ML code
    out of a monadic computation ;

    (ii) compile the resulting ML module that depends on the 
    plugin itself ;

    (iii) dynamically load the ML module which has the effect of
    triggerring the evaluation of the monadic computation.

    The communication between the compiled code and the plugin is
    implemented by the module {!CybeleState}.
*)

open Tacmach
open Entries
open Declarations
open Declare

(** {1 Helper functions} *)

(** [define c] introduces a fresh constant name for the term [c]. *)
let define c =
  let fresh_name =
  (** We will use the string "cybele" as a prefix to name the
      monadic computation we want to compile. *)
    let base = Names.id_of_string "cybele" in

  (** [is_visible_name id] returns [true] if [id] is already
      used on the Coq side. *)
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (** Safe fresh name generation. *)
    Namegen.next_ident_away_from base is_visible_name
  in
  ignore (
    declare_constant ~internal:KernelVerbose fresh_name
      (DefinitionEntry {
        const_entry_body = c;
        const_entry_secctx = None;
        const_entry_type = None;
        const_entry_opaque = false;
        const_entry_inline_code = false
       },
       Decl_kinds.IsDefinition Decl_kinds.Definition)
  );
  fresh_name

(** [command s] runs [s] and logs the exit status. *)
let command s =
  let ret = Sys.command s in
  Pp.msg_info (Pp.str (Printf.sprintf "Cybele [%d]: %s\n" ret s))

let cleanup fname =
  command (Printf.sprintf "rm %s" fname)

let patch_ocaml_file file_name patch =
  let channel = open_out_gen [Open_append] 0 file_name in
  output_string channel patch;
  close_out channel

(** [time l f] runs [f ()] displaying its running time. *)
let time l f = 
  let start = System.get_time () in
  let y = f () in
  let stop = System.get_time () in 
  Pp.msg_info (Pp.str 
                 (Printf.sprintf "Running time of the %s: %f secs\n"
                    l
                    (System.time_difference start stop)));
  y

(** {1 Compilation} *)

(** Use site configuration to determine where Cybele
    is installed. *)
let coqlib =
  let coqlib =
    Envars.coqlib (fun _ ->
      Errors.error
        "Cybele: unable to obtain information about the site configuration."
    )
  in
  Filename.concat (Filename.concat coqlib "user-contrib") "Cybele"

(** Use site configuration to use the right ocaml native compilers. *)
let ocamlopt = Envars.ocamlopt ()

(** Use site configuration to use the right ocaml bytecode compilers. *)
let ocamlc = Envars.ocamlc ()

(** compile [c] returns a compiled version of the monadic computation [c]
    in the form of an Ocaml module. *)
let compile c =
  let rec compile () =
    (** The compilation is the composition of the Coq extraction
        with the compilation from ocaml to the right low-level
        plateform (native or bytecode).

        The extraction uses a temporary definition that is automatically
        cleaned up using the Coq's rollback mechanism.
    *)
    ocaml_compiler (States.with_state_protection ocaml_via_extraction ())

  and ocaml_via_extraction () =
    (** Name [c]. *)
    let constant = define c in
    (** Extract [c] in a file and all its dependencies. *)
    let tmp      = Filename.temp_file "cybele" ".ml" in
    let tmp_intf = Filename.chop_extension tmp ^ ".mli" in
    time "the extraction" (fun () -> 
      Extract_env.full_extraction (Some tmp) [
        Libnames.Ident (Loc.ghost, constant)
      ]);
    (** We are not interested in the interface file. *)
    cleanup tmp_intf;
    tmp

  and ocaml_compiler fname =
    (** Use a temporary file for the compiled module. *)
    let compiled_module =
      let basename = Filename.temp_file "cybele_dyn" "" in
      fun ext -> basename ^ "." ^ ext 
    in
    (** Compile using the right compiler. *)
    if Dynlink.is_native then (
      time "the compilation of the ocaml code" (fun () ->
        let target  = compiled_module "cmx" in
        let target' = compiled_module "cmxs" in
        command (Printf.sprintf
                   "%s -rectypes -c -I %s -o %s %s"
                   ocamlopt coqlib target fname);
        command (Printf.sprintf
                   "%s -shared -o %s %s"
                   ocamlopt target' target);
        (target', [target; target'])
      )
    ) else (
      let target = compiled_module "cmo" in
      time "the compilation of the ocaml code" (fun () ->
        command (Printf.sprintf 
                   "%s -rectypes -c -linkall -I %s -o %s %s/cybelePlugin.cma %s"
                   ocamlc coqlib target coqlib fname);
        (target, [target]))
    )
  in
  compile ()

(* FIXME: Dynamic loading is probably not the right way of doing it as
   OCaml do not provide a way to unload code... We better use
   marshalling-based communication in the future. *)
let dynload f =
  try
    Dynlink.loadfile f
  with Dynlink.Error e ->
    Errors.error ("Cybele (during compiled code loading):"
                   ^ (Dynlink.error_message e))

(* FIXME: Implement a sanity check to make sure that dynamic
   compilation and execution is possible. *)
let sanity_check () =
  ()

(** {1 Main entry} *)

(** The oracle compilation and execution. *)
let compile_and_run_oracle c =
  sanity_check ();
  let dyncode, files = compile c in
  time "the extracted code" (fun () -> dynload dyncode);
  List.iter cleanup files

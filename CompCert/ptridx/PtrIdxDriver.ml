(* ptridxgen: C source -> Clight -> pointer-arithmetic refactoring.

   For each input foo.c, writes into the output directory (-outdir, default
   the current directory):
     foo.light.c      the resulting Clight, printed as C
     foo.ptridx.json  facts about the run
     foo.v            with -rocq: the same program as a Rocq AST, as clightgen prints it
     foo.o            with -c: the same program compiled by CompCert's backend

   The Clight is produced exactly as clightgen does it (SimplExpr, then
   SimplLocals). With -no-pass the refactoring is skipped, so the outputs
   equal clightgen's. *)

open Printf
open Commandline
open CommonOptions
open Driveraux
open Frontend
open Diagnostics

let tool_name = "pointer-arithmetic refactoring (ptridxgen)"

let option_pass = ref true
let option_memory = ref false   (* caches for pointers stored in memory: unverified, opt-in *)
let option_outdir = ref Filename.current_dir_name

let out_file sourcename suffix =
  Filename.concat !option_outdir
    (Filename.remove_extension (Filename.basename sourcename) ^ suffix)

let to_clight sourcename csyntax =
  let loc = file_loc sourcename in
  match SimplExpr.transl_program csyntax with
  | Errors.Error msg -> fatal_error loc "%a" print_error msg
  | Errors.OK p ->
      match SimplLocals.transf_program p with
      | Errors.Error msg -> fatal_error loc "%a" print_error msg
      | Errors.OK p' -> p'

(* Names for the new temporaries. A pointer is named after the source
   variable, or tNNN for a temporary SimplExpr introduced; its base and index
   are <name>_base and <name>_idx, made unique. Registering them lets both
   printers show the names instead of numbers. *)

let display_name id =
  try Hashtbl.find Camlcoq.string_of_atom id
  with Not_found -> sprintf "$%d" (Camlcoq.P.to_int id)

let stem_name id =
  try Hashtbl.find Camlcoq.string_of_atom id
  with Not_found -> sprintf "t%d" (Camlcoq.P.to_int id)

let register id stem =
  if not (Hashtbl.mem Camlcoq.string_of_atom id) then begin
    let rec pick n =
      let s = if n = 0 then stem else sprintf "%s_%d" stem n in
      if Hashtbl.mem Camlcoq.atom_of_string s then pick (n + 1) else s in
    let name = pick 0 in
    Hashtbl.replace Camlcoq.atom_of_string name id;
    Hashtbl.replace Camlcoq.string_of_atom id name
  end

(* A cached location is named after its path: r_pos for r->pos, cursor for
   a global cursor, pp_deref for *pp. *)
let rec loc_stem = function
  | Clight.Evar (x, _) -> stem_name x
  | Clight.Efield (Clight.Ederef (Clight.Etempvar (t, _), _), f, _) -> stem_name t ^ "_" ^ Camlcoq.extern_atom f
  | Clight.Efield (b, f, _) -> loc_stem b ^ "_" ^ Camlcoq.extern_atom f
  | Clight.Ederef (Clight.Etempvar (t, _), _) -> stem_name t ^ "_deref"
  | _ -> "mem"

(* A location as C text, without the $ that marks temporaries. *)
let loc_text e =
  String.concat "" (String.split_on_char '$' (Format.asprintf "%a" PrintClight.print_expr e))

(* The refactored program, and per function the pointers that were split and
   the locations cached. A base shared by a group is named after its first
   member registered, so parameters come first, then source variables, then
   temporaries that SimplExpr introduced. *)
let refactor clight =
  if not !option_pass then (clight, []) else begin
    let (prog, plan) = PtrIdx.transf_program_plan true !option_memory clight in
    List.iter (fun (_, ((_, splits), caches)) ->
      let params, others = List.partition (fun (_, s) -> s.PtrIdx.sp_param) splits in
      let named, temps = List.partition (fun (p, _) -> Hashtbl.mem Camlcoq.string_of_atom p) others in
      List.iter (fun (p, s) ->
        register s.PtrIdx.sp_base (stem_name p ^ "_base");
        register s.PtrIdx.sp_idx (stem_name p ^ "_idx")) (params @ named @ temps);
      List.iter (fun k ->
        let stem = loc_stem k.PtrIdx.ca_loc in
        register k.PtrIdx.ca_base (stem ^ "_base");
        register k.PtrIdx.ca_idx (stem ^ "_idx")) caches) plan;
    (* Report functions that were rewritten or that fell back. *)
    (prog, List.filter (fun (_, ((fell_back, splits), caches)) -> fell_back || splits <> [] || caches <> []) plan)
  end

let with_formatter file f =
  let oc = open_out file in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
    let fmt = Format.formatter_of_out_channel oc in
    f fmt;
    Format.pp_print_flush fmt ())

let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (function
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | c when Char.code c < 0x20 -> Buffer.add_string b (sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b

(* temporaries: pointer temporaries are split; memory: pointers stored in
   memory are cached too (with -memory). *)
let pass_name () = if !option_memory then "temporaries, memory" else "temporaries"

let json_split (p, s) =
  sprintf "{\"pointer\": %s, \"base\": %s, \"index\": %s, \"elem_size\": %d}"
    (json_string (display_name p)) (json_string (display_name s.PtrIdx.sp_base))
    (json_string (display_name s.PtrIdx.sp_idx)) (Camlcoq.Z.to_int s.PtrIdx.sp_size)

let json_cache k =
  sprintf "{\"location\": %s, \"base\": %s, \"index\": %s, \"elem_size\": %d}"
    (json_string (loc_text k.PtrIdx.ca_loc)) (json_string (display_name k.PtrIdx.ca_base))
    (json_string (display_name k.PtrIdx.ca_idx)) (Camlcoq.Z.to_int k.PtrIdx.ca_size)

let json_function (f, ((fell_back, splits), caches)) =
  sprintf "    {\"name\": %s, \"fallback\": %b, \"split\": [%s], \"cached\": [%s]}"
    (json_string (display_name f)) fell_back (String.concat ", " (List.map json_split splits))
    (String.concat ", " (List.map json_cache caches))

(* -rocq: also print the program as a Rocq AST (foo.v). Off by default: for a
   large file it is huge (238 MB for libfor's test.c) and costly to print. *)
let option_rocq = ref false

(* -valid-c: print the Clight as plain C that clang accepts
   (PrintClightC), not in PrintClight's C-like syntax. *)
let option_valid_c = ref false

let write_outputs sourcename cast (prog, plan) =
  with_formatter (out_file sourcename ".light.c") (fun fmt ->
    match cast with
    | Some ast -> PrintClightC.print_program ast fmt prog
    | None -> PrintClight.print_program PrintClight.Clight2 fmt prog);
  if !option_rocq then
    with_formatter (out_file sourcename ".v") (fun fmt ->
      ExportClight.print_program fmt prog sourcename false);
  with_formatter (out_file sourcename ".ptridx.json") (fun fmt ->
    Format.fprintf fmt "{\n  \"tool\": \"ptridxgen\",\n  \"source\": %s,\n  \"refactored\": %b,\n  \
                        \"pass\": %s,\n  \"functions\": [%s%s%s]\n}\n"
      (json_string sourcename) !option_pass (json_string (pass_name ()))
      (if plan = [] then "" else "\n") (String.concat ",\n" (List.map json_function plan))
      (if plan = [] then "" else "\n  "))

(* -c: compile the resulting Clight with CompCert's own backend into foo.o.
   Compiler.transf_clight_program would run SimplLocals again, but the
   program is already past it (semantics2, as Cshmgen expects), so the rest
   of the chain is run directly. *)
let option_compile = ref false

let compile_clight sourcename prog =
  let ( >>= ) r f = match r with Errors.OK x -> f x | Errors.Error m -> Errors.Error m in
  let asm =
    match Compiler.apply_partial
            (Cshmgen.transl_program prog >>= Cminorgen.transl_program >>= Compiler.transf_cminor_program)
            Asmexpand.expand_program with
    | Errors.OK asm -> asm
    | Errors.Error msg -> fatal_error (file_loc sourcename) "%a" print_error msg in
  let asmname = tmp_file ".s" in
  let oc = open_out asmname in
  PrintAsm.print_program oc asm;
  close_out oc;
  Assembler.assemble asmname (out_file sourcename ".o")

(* Frontend.parse_c_file, also returning the C AST (-valid-c reads the
   va_list types from it). *)
let parse_c_file_with_ast sourcename ifile =
  Debug.init_compile_unit sourcename;
  Sections.initialize();
  CPragmas.reset();
  let ast =
    Parse.preprocessed_file
      ~unblock: true
      ~switch_norm: (if !Clflags.option_funstructured_switch then `Full else `Partial)
      ~struct_passing: !Clflags.option_fstruct_passing
      ~packed_structs: !Clflags.option_fpacked_structs
      sourcename ifile in
  (ast, C2C.convertProgram ast)

let process_c_file sourcename =
  ensure_inputfile_exists sourcename;
  let preproname = tmp_file ".i" in
  preprocess sourcename preproname;
  let (cast, csyntax) =
    if !option_valid_c then
      let (ast, csyntax) = parse_c_file_with_ast sourcename preproname in (Some ast, csyntax)
    else (None, parse_c_file sourcename preproname) in
  let (prog, plan) = refactor (to_clight sourcename csyntax) in
  write_outputs sourcename cast (prog, plan);
  if !option_compile then compile_clight sourcename prog

let usage_string =
  version_string tool_name ^
{|Usage: ptridxgen [options] <source files>
For each .c file, writes <file>.light.c, <file>.v and <file>.ptridx.json.
Processing options:
  -no-pass       Skip the refactoring (outputs equal clightgen's)
  -memory        Also cache pointers stored in memory (not covered by the proof)
  -no-memory     Leave pointers stored in memory alone (the default)
  -c             Also compile the resulting Clight with CompCert's backend into <file>.o
  -rocq          Also print the program as a Rocq AST into <file>.v
  -valid-c       Print <file>.light.c as plain C that clang accepts
  -outdir <dir>  Directory for the outputs (default: current directory)
  -canonical-idents  Use canonical numbers to represent identifiers  (default)
  -short-idents  Use small, non-canonical numbers to represent identifiers
|} ^
prepro_help ^
language_support_help ^
general_help ^
warning_help

let print_usage_and_exit () =
  printf "%s" usage_string; exit 0

(* Files are processed after the whole command line is parsed, so options
   apply regardless of their position. *)
let actions : (unit -> unit) list ref = ref []
let num_input_files = ref 0

let cmdline_actions =
  [ Exact "-help", Unit print_usage_and_exit;
    Exact "--help", Unit print_usage_and_exit ]
  @ version_options tool_name
  @ [ Exact "-no-pass", Unset option_pass;
      Exact "-memory", Set option_memory;
      Exact "-no-memory", Unset option_memory;
      Exact "-c", Set option_compile;
      Exact "-rocq", Set option_rocq;
      Exact "-valid-c", Set option_valid_c;
      Exact "-outdir", String (fun s -> option_outdir := s);
      Exact "-canonical-idents", Set Camlcoq.use_canonical_atoms;
      Exact "-short-idents", Unset Camlcoq.use_canonical_atoms ]
  @ prepro_actions
  @ general_options
  @ warning_options
  @ language_support_options
  @ [ Prefix "-", Self (fun s -> fatal_error no_loc "Unknown option `%s'" s);
      Suffix ".c", Self (fun s ->
        incr num_input_files; actions := (fun () -> process_c_file s) :: !actions) ]

let _ =
  try
    Gc.set { (Gc.get()) with
               Gc.minor_heap_size = 524288;
               Gc.major_heap_increment = 4194304 };
    Printexc.record_backtrace true;
    Camlcoq.use_canonical_atoms := true;
    Frontend.init ();
    parse_cmdline cmdline_actions;
    if !num_input_files = 0 then fatal_error no_loc "no input file";
    List.iter (fun act -> act ()) (List.rev !actions)
  with
  | Sys_error msg
  | CmdError msg -> error no_loc "%s" msg; exit 2
  | Abort -> exit 2
  | e -> crash e

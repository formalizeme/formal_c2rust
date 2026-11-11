(* Clight printed as plain C that clang accepts (ptridxgen -valid-c).

   A utility outside the verified pass. *)

open Format
open Camlcoq
open AST
open Ctypes
open Cop
open Clight

(* ** Names *)

let is_ident s =
  s <> ""
  && (match s.[0] with 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false)
  && String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true | _ -> false) s

let atom_name id = Hashtbl.find_opt string_of_atom id

(* Names this printer made up, so that two never collide. *)
let taken : (string, unit) Hashtbl.t = Hashtbl.create 101

let fresh base =
  let free s = not (Hashtbl.mem atom_of_string s || Hashtbl.mem taken s) in
  let rec pick n =
    let s = if n = 0 then base else sprintf "%s_%d" base n in
    if free s then s else pick (n + 1) in
  let s = pick 0 in
  Hashtbl.replace taken s ();
  s

(* <anon>_0 -> anon_0, @1 -> _1 *)
let sanitize s =
  let s = String.concat "" (String.split_on_char '<' (String.concat "" (String.split_on_char '>' s))) in
  let s = String.map (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' as c -> c | _ -> '_') s in
  if is_ident s then s else "c2r_" ^ s

let is_func_name s = s = "__func__" || String.starts_with ~prefix:"__func____" s

(* CompCert builtins that clang knows under another name. *)
let builtin_renames = [ "__builtin_fsqrt", "__builtin_sqrt"; "__builtin_bswap", "__builtin_bswap32" ]

let global_names : (ident, string) Hashtbl.t = Hashtbl.create 101

(* The name of a global, composite, member or label. *)
let gname id =
  match Hashtbl.find_opt global_names id with
  | Some s -> s
  | None ->
      let s =
        match atom_name id with
        | Some s when is_func_name s -> fresh "c2r_func"
        | Some s when List.mem_assoc s builtin_renames -> List.assoc s builtin_renames
        | Some s when is_ident s -> s
        | Some s -> fresh (sanitize s)
        | None -> fresh (sprintf "c2r_%d" (P.to_int id)) in
      Hashtbl.replace global_names id s;
      s

let is_func_atom id = match atom_name id with Some s -> is_func_name s | None -> false

(* ** Types from the C AST, for va_list *)

type hints = {
  typedefs: (int, C.typ) Hashtbl.t;                (* typedef stamp -> type *)
  funs: (string, C.typ) Hashtbl.t;                 (* function -> its TFun *)
  locals: (string * string, C.typ) Hashtbl.t;      (* (function, variable) -> type *)
  globals: (string, C.typ) Hashtbl.t
}

let hints = {
  typedefs = Hashtbl.create 101; funs = Hashtbl.create 101;
  locals = Hashtbl.create 101; globals = Hashtbl.create 101 }

let rec is_valist t =
  match t with
  | C.TNamed (id, _) ->
      id.C.name = "__builtin_va_list"
      || (match Hashtbl.find_opt hints.typedefs id.C.stamp with Some t' -> is_valist t' | None -> false)
  | _ -> false

let rec unroll t =
  match t with
  | C.TNamed (id, _) when not (is_valist t) ->
      (match Hashtbl.find_opt hints.typedefs id.C.stamp with Some t' -> unroll t' | None -> t)
  | _ -> t

let is_valist_opt = function Some t -> is_valist t | None -> false

let read_hints (p: C.program) =
  Hashtbl.reset hints.typedefs; Hashtbl.reset hints.funs;
  Hashtbl.reset hints.locals; Hashtbl.reset hints.globals;
  let rec locals_of fn s =
    match s.C.sdesc with
    | C.Sdecl (_, id, t, _) -> Hashtbl.replace hints.locals (fn, id.C.name) t
    | C.Sseq (a, b) | C.Sif (_, a, b) -> locals_of fn a; locals_of fn b
    | C.Swhile (_, a) | C.Sdowhile (a, _) | C.Sswitch (_, a) | C.Slabeled (_, a) -> locals_of fn a
    | C.Sfor (a, _, b, c) -> locals_of fn a; locals_of fn b; locals_of fn c
    | C.Sblock l -> List.iter (locals_of fn) l
    | _ -> () in
  List.iter (fun g ->
    match g.C.gdesc with
    | C.Gtypedef (id, t) -> Hashtbl.replace hints.typedefs id.C.stamp t
    | C.Gdecl (_, id, t, _) ->
        (match unroll t with
         | C.TFun _ -> Hashtbl.replace hints.funs id.C.name t
         | _ -> Hashtbl.replace hints.globals id.C.name t)
    | C.Gfundef fd ->
        let fn = fd.C.fd_name.C.name in
        Hashtbl.replace hints.funs fn (C.TFun (fd.C.fd_ret, Some fd.C.fd_params, fd.C.fd_vararg, []));
        List.iter (fun (id, t) -> Hashtbl.replace hints.locals (fn, id.C.name) t) fd.C.fd_params;
        List.iter (fun (_, id, t, _) -> Hashtbl.replace hints.locals (fn, id.C.name) t) fd.C.fd_locals;
        locals_of fn fd.C.fd_body
    | _ -> ()) p

(* ** Printing types *)

let ce = ref (Maps.PTree.empty : composite_env)

let aligned n = sprintf "__attribute__((aligned(%Ld)))" n

let attrs align a =
  (if a.attr_volatile then " volatile" else "")
  ^ (match a.attr_alignas with
     | Some l when align -> " " ^ aligned (Int64.shift_left 1L (N.to_int l))
     | _ -> "")

let optid id = if id = "" then "" else " " ^ id

(* CompCert's char is unsigned (aarch64), as is plain char there; its long
   long is 64 bits, as is long. Printing char and long keeps the code
   consistent with the C library and with string literals. *)
let int_name sz sg = if sz = I8 && sg = Unsigned then "char" else PrintCsyntax.name_inttype sz sg
let long_name sg = if sg = Signed then "long" else "unsigned long"

(* The attributes of a C type, including those of the typedefs it goes through. *)
let rec hint_attrs t =
  match t with
  | C.TNamed (_, a) -> a @ (match unroll t with C.TNamed _ -> [] | t' -> hint_attrs t')
  | C.TVoid a | C.TInt (_, a) | C.TFloat (_, a) | C.TPtr (_, a) | C.TArray (_, _, a)
  | C.TFun (_, _, _, a) | C.TStruct (_, a) | C.TUnion (_, a) | C.TEnum (_, a) -> a

let const_of consts hint =
  match hint with
  | Some t when consts && List.mem C.AConst (hint_attrs t) -> "const "
  | _ -> ""

(* [id] declared with type [ty]. [hint] is the C AST type of the same
   declaration, if known; [va i] says that parameter [i] of a function type
   is a va_list. [align] allows alignment, which only a variable or member
   declaration may carry. [exact] takes long long from [hint] and, with
   [consts], its const qualifiers: a declaration of a C library function
   must match the library's. *)
let rec cdecl ?(align = false) ?(exact = false) ?(consts = false) ?(va = fun _ -> false) ?hint id ty =
  if is_valist_opt hint then "__builtin_va_list" ^ optid id
  else
  let cq = const_of consts hint in
  let hint = Option.map unroll hint in
  match ty with
  | Tvoid -> cq ^ "void" ^ optid id
  | Tint (sz, sg, a) -> cq ^ int_name sz sg ^ attrs align a ^ optid id
  | Tfloat (sz, a) -> cq ^ PrintCsyntax.name_floattype sz ^ attrs align a ^ optid id
  | Tlong (sg, a) ->
      let n = match hint, sg with
        | Some (C.TInt ((C.ILongLong | C.IULongLong), _)), Signed when exact -> "long long"
        | Some (C.TInt ((C.ILongLong | C.IULongLong), _)), Unsigned when exact -> "unsigned long long"
        | _ -> long_name sg in
      cq ^ n ^ attrs align a ^ optid id
  | Tpointer (t, a) ->
      let hint' = match hint with Some (C.TPtr (t', _) | C.TArray (t', _, _)) -> Some t' | _ -> None in
      let q = (if a.attr_volatile then " volatile " else "") ^ (if cq = "" then "" else " const ") in
      let paren = (match t with Tfunction _ | Tarray _ -> true | _ -> false) && not (is_valist_opt hint') in
      let id' = if paren then sprintf "(*%s%s)" q id else sprintf "*%s%s" q id in
      (* Only the pointed-to type gets const: C adds no const deeper down,
         and the functions passed as callbacks have none. *)
      let exact', consts' = match t with
        | Tfunction _ -> false, false
        | Tpointer _ -> exact, false
        | _ -> exact, consts in
      cdecl ~exact:exact' ~consts:consts' ?hint:hint' id' t
  | Tarray (t, n, _) ->
      let hint' = match hint with Some (C.TArray (t', _, _)) -> Some t' | _ -> None in
      cdecl ~align ~exact ~consts ?hint:hint' (sprintf "%s[%s]" id (Z.to_string n)) t
  | Tfunction (args, res, cc) ->
      let hres, hargs =
        match hint with
        | Some (C.TFun (r, ps, _, _)) -> Some r, (match ps with Some l -> List.map snd l | None -> [])
        | _ -> None, [] in
      let params =
        List.mapi (fun i t ->
          if va i then "__builtin_va_list"
          else cdecl ~exact ~consts:exact ?hint:(List.nth_opt hargs i) "" t) args in
      let id' = if id = "" then "(*)" else id in
      cdecl ~exact ?hint:hres (sprintf "%s(%s)" id' (param_list cc params)) res
  | Tstruct (n, a) -> cq ^ "struct " ^ gname n ^ attrs align a ^ optid id
  | Tunion (n, a) -> cq ^ "union " ^ gname n ^ attrs align a ^ optid id

and param_list cc params =
  if cc.cc_unproto then ""
  else match params, cc.cc_vararg with
    | [], None -> "void"
    | [], Some _ -> "..."
    | l, None -> String.concat ", " l
    | l, Some _ -> String.concat ", " l ^ ", ..."

let name_type ty = cdecl "" ty

(* ** Literals *)

let decimal digits ok x =
  let rec go n =
    if n > digits then sprintf "%h" x
    else let s = sprintf "%.*g" n x in if ok s then s else go (n + 1) in
  let s = go 6 in
  if String.exists (fun c -> c = '.' || c = 'e' || c = 'x') s then s else s ^ ".0"

let double_literal x =
  if Float.is_nan x then "__builtin_nan(\"\")"
  else if x = Float.infinity then "__builtin_inf()"
  else if x = Float.neg_infinity then "-__builtin_inf()"
  else decimal 17 (fun s -> Int64.equal (Int64.bits_of_float (float_of_string s)) (Int64.bits_of_float x)) x

let single_literal x =
  if Float.is_nan x then "__builtin_nanf(\"\")"
  else if x = Float.infinity then "__builtin_inff()"
  else if x = Float.neg_infinity then "-__builtin_inff()"
  else decimal 9 (fun s -> Int32.equal (Int32.bits_of_float (float_of_string s)) (Int32.bits_of_float x)) x ^ "f"

let int_literal ty (n: int32) =
  match ty with
  | Tint (I32, Unsigned, _) -> sprintf "%luU" n
  | _ -> if n = Int32.min_int then "(-2147483647 - 1)" else sprintf "%ld" n

let long_literal ty (n: int64) =
  match ty with
  | Tlong (Unsigned, _) -> sprintf "%LuUL" n
  | _ -> if n = Int64.min_int then "(-9223372036854775807L - 1)" else sprintf "%LdL" n

let c_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  let prev = ref ' ' in
  String.iter (fun c ->
    (match c with
     | '"' -> Buffer.add_string b "\\\""
     | '\\' -> Buffer.add_string b "\\\\"
     | '\n' -> Buffer.add_string b "\\n"
     | '\t' -> Buffer.add_string b "\\t"
     | '\r' -> Buffer.add_string b "\\r"
     | '?' when !prev = '?' -> Buffer.add_string b "\\?"      (* no trigraphs *)
     | ' '..'~' -> Buffer.add_char b c
     | _ -> Buffer.add_string b (sprintf "\\%03o" (Char.code c)));
    prev := c) s;
  Buffer.add_char b '"';
  Buffer.contents b

(* ** va_list *)

(* The C library functions with a va_list parameter, and its position. *)
let libc_va = [
  "vprintf", 1; "vfprintf", 2; "vsprintf", 2; "vsnprintf", 3; "vasprintf", 2; "vdprintf", 2;
  "vscanf", 1; "vfscanf", 2; "vsscanf", 2; "__isoc99_vscanf", 1; "__isoc99_vfscanf", 2;
  "__isoc99_vsscanf", 2; "vsyslog", 2; "verr", 2; "verrx", 2; "vwarn", 1; "vwarnx", 1;
  "vwprintf", 1; "vfwprintf", 2; "vswprintf", 3; "vwscanf", 1; "vfwscanf", 2; "vswscanf", 2;
  "obstack_vprintf", 2; "__vprintf_chk", 2; "__vfprintf_chk", 3; "__vsprintf_chk", 4;
  "__vsnprintf_chk", 5; "__vasprintf_chk", 3; "__vdprintf_chk", 3 ]

(* va_arg as CompCert lowers it, and the type to read. *)
let va_arg_type = function
  | "__compcert_va_int32" -> Some "unsigned int"
  | "__compcert_va_int64" -> Some "unsigned long"
  | "__compcert_va_float64" -> Some "double"
  | _ -> None

let callee_name = function Evar (g, _) -> atom_name g | _ -> None

let fundefs : (ident, Clight.fundef) Hashtbl.t = Hashtbl.create 101

(* Unprototyped functions get their arguments at the promoted types of the
   call: the types of each function's calls, if they all agree. *)
let kr_args : (ident, Ctypes.coq_type list option) Hashtbl.t = Hashtbl.create 17

let promoted args = List.map (fun a -> default_argument_conversion (typeof a)) args

let param_type g i =
  match Hashtbl.find_opt fundefs g with
  | Some (Internal f) -> Option.map snd (List.nth_opt f.fn_params i)
  | Some (External (_, args, _, _)) -> List.nth_opt args i
  | None -> None

(* A va_list parameter, after the array type decays (AAPCS64). *)
let decayed_va = function Some (Tpointer (Tlong (Unsigned, _), _)) -> true | _ -> false

(* (function, parameter position) pairs that are va_list. *)
let va_params : (ident * int, unit) Hashtbl.t = Hashtbl.create 17

(* (function, variable) pairs that hold a decayed va_list: parameters, and
   the locals CompCert copies them into or that receive them. *)
let va_vars : (ident * ident, unit) Hashtbl.t = Hashtbl.create 17

(* ** Functions being printed *)

type fctx = {
  fid: ident;
  fname: string;
  f: coq_function;
  temps: (ident, string) Hashtbl.t;       (* parameters and temporaries *)
  vars: (ident, unit) Hashtbl.t;
  mutable labels: int
}

let fctx_of fid f =
  let vars = Hashtbl.create 17 in
  List.iter (fun (v, _) -> Hashtbl.replace vars v ()) f.fn_vars;
  { fid; fname = gname fid; f; temps = Hashtbl.create 17; vars; labels = 0 }

let tname ctx id = match Hashtbl.find_opt ctx.temps id with Some s -> s | None -> gname id

let rec index_of x i = function
  | [] -> None
  | (y, _) :: l -> if P.eq x y then Some i else index_of x (i + 1) l

let local_hint ctx id =
  match atom_name id with Some n -> Hashtbl.find_opt hints.locals (ctx.fname, n) | None -> None

let rec strip_casts = function Ecast (e, _) -> strip_casts e | e -> e

(* Is [e] a va_list (a local or global va_list, a va_list parameter, or
   [*p] with [p] a pointer to a va_list)? *)
let rec is_va_value ctx e =
  match e with
  | Evar (x, _) ->
      Hashtbl.mem va_vars (ctx.fid, x)
      || is_valist_opt (if Hashtbl.mem ctx.vars x then local_hint ctx x
                        else Option.bind (atom_name x) (Hashtbl.find_opt hints.globals))
  | Etempvar (p, _) -> Hashtbl.mem va_vars (ctx.fid, p)
  | Ederef (Etempvar (q, _), _) ->
      (match Option.map unroll (local_hint ctx q) with Some (C.TPtr (t, _)) -> is_valist t | _ -> false)
  | Ecast (e', _) -> is_va_value ctx e'
  | _ -> false

let rec iter_stmt fn s =
  fn s;
  match s with
  | Ssequence (s1, s2) | Sifthenelse (_, s1, s2) | Sloop (s1, s2) -> iter_stmt fn s1; iter_stmt fn s2
  | Slabel (_, s1) -> iter_stmt fn s1
  | Sswitch (_, ls) ->
      let rec cases = function LSnil -> () | LScons (_, s, rem) -> iter_stmt fn s; cases rem in
      cases ls
  | _ -> ()

(* Which parameters and locals are va_list: seeded by the C library and by
   va_arg, then propagated through calls, copies and va_copy until nothing
   changes. *)
let infer_va prog =
  Hashtbl.reset va_params; Hashtbl.reset va_vars;
  let changed = ref true in
  let mark_param g i =
    if not (Hashtbl.mem va_params (g, i)) && decayed_va (param_type g i) then begin
      Hashtbl.replace va_params (g, i) (); changed := true;
      match Hashtbl.find_opt fundefs g with
      | Some (Internal f) ->
          (match List.nth_opt f.fn_params i with
           | Some (x, _) -> Hashtbl.replace va_vars (g, x) ()
           | None -> ())
      | _ -> ()
    end in
  List.iter (fun (id, gd) ->
    match gd, atom_name id with
    | Gfun (External _), Some n -> List.iter (fun (m, i) -> if m = n then mark_param id i) libc_va
    | _ -> ()) prog.prog_defs;
  let funs = List.filter_map (fun (id, gd) ->
    match gd with Gfun (Internal f) -> Some (fctx_of id f) | _ -> None) prog.prog_defs in
  while !changed do
    changed := false;
    List.iter (fun ctx ->
      let f = ctx.f in
      let mark_var x =
        match index_of x 0 f.fn_params with
        | Some i -> mark_param ctx.fid i
        | None ->
            let ty = match List.assoc_opt x f.fn_temps with
              | Some t -> Some t
              | None -> List.assoc_opt x f.fn_vars in
            if not (Hashtbl.mem va_vars (ctx.fid, x)) && decayed_va ty then begin
              Hashtbl.replace va_vars (ctx.fid, x) (); changed := true
            end in
      let mark e =
        match strip_casts e with
        | Etempvar (x, _) | Evar (x, _) -> mark_var x
        | _ -> () in
      let copy x e =
        if is_va_value ctx e then mark_var x;
        if Hashtbl.mem va_vars (ctx.fid, x) then mark e in
      iter_stmt (function
        | Scall (_, callee, a :: _) when Option.bind (callee_name callee) va_arg_type <> None -> mark a
        | Scall (_, Evar (g, _), args) ->
            List.iteri (fun i a ->
              if is_va_value ctx a then mark_param g i;
              if Hashtbl.mem va_params (g, i) then mark a) args
        | Sset (x, e) | Sassign (Evar (x, _), e) -> copy x e
        | Sbuiltin (_, EF_memcpy _, _, [d; s]) ->
            if is_va_value ctx d then mark s;
            if is_va_value ctx s then mark d
        | _ -> ()) f.fn_body) funs
  done

(* ** Expressions *)

type associativity = LtoR | RtoL | NA

let negative = function
  | Econst_int (_, Tint (I32, Unsigned, _)) | Econst_long (_, Tlong (Unsigned, _)) -> false
  | Econst_int (n, Tint _) -> camlint_of_coqint n < 0l
  | Econst_long (n, Tlong _) -> camlint64_of_coqint n < 0L
  | Econst_float (f, _) -> Float.sign_bit (camlfloat_of_coqfloat f)
  | Econst_single (f, _) -> Float.sign_bit (camlfloat_of_coqfloat32 f)
  | _ -> false

let precedence = function
  | Evar _ | Etempvar _ -> (16, NA)
  | e when negative e -> (15, RtoL)
  | Econst_int (_, Tint _) | Econst_long (_, Tlong _) | Econst_float _ | Econst_single _ -> (16, NA)
  | Econst_int _ | Econst_long _ -> (14, RtoL)            (* printed with a cast *)
  | Efield _ -> (16, LtoR)
  | Ederef _ | Eunop _ | Eaddrof _ | Esizeof _ | Ealignof _ -> (15, RtoL)
  | Ecast _ -> (14, RtoL)
  | Ebinop ((Omul | Odiv | Omod), _, _, _) -> (13, LtoR)
  | Ebinop ((Oadd | Osub), _, _, _) -> (12, LtoR)
  | Ebinop ((Oshl | Oshr), _, _, _) -> (11, LtoR)
  | Ebinop ((Olt | Ogt | Ole | Oge), _, _, _) -> (10, LtoR)
  | Ebinop ((Oeq | One), _, _, _) -> (9, LtoR)
  | Ebinop (Oand, _, _, _) -> (8, LtoR)
  | Ebinop (Oxor, _, _, _) -> (7, LtoR)
  | Ebinop (Oor, _, _, _) -> (6, LtoR)

(* A va_list passed on is printed without the casts Clight added. *)
let rec drop_va_casts ctx e =
  match e with
  | Ecast (e', _) when is_va_value ctx e' -> drop_va_casts ctx e'
  | _ -> e

let var_name id = if is_func_atom id then "__func__" else gname id

(* A comparison of signed with unsigned converts the signed operand;
   written out, as clang wants (-Wsign-compare). *)
let signed_after_promotion = function
  | Tint (I32, Signed, _) | Tint ((I8 | I16), _, _) | Tlong (Signed, _) -> true
  | _ -> false

let compared a1 a2 =
  let t1 = typeof a1 and t2 = typeof a2 in
  match classify_binarith t1 t2 with
  | Coq_bin_case_i Unsigned | Coq_bin_case_l Unsigned as c ->
      let conv a t = if signed_after_promotion t then Ecast (a, binarith_type c) else a in
      (conv a1 t1, conv a2 t2)
  | _ -> (a1, a2)

(* Operands that clang wants parenthesized (-Wparentheses). *)
let clarify op e =
  match op, e with
  | (Oshl | Oshr), Ebinop ((Oadd | Osub), _, _, _)
  | (Oor | Oxor), Ebinop (Oand, _, _, _)
  | Oor, Ebinop (Oxor, _, _, _) -> true
  | _ -> false

let rec expr ctx p (prec, e) =
  let e = drop_va_casts ctx e in
  let (prec', assoc) = precedence e in
  let (prec1, prec2) = if assoc = LtoR then (prec', prec' + 1) else (prec' + 1, prec') in
  let paren = prec' < prec in
  if paren then fprintf p "@[<hov 2>(" else fprintf p "@[<hov 2>";
  begin match e with
  | Evar (id, _) -> fprintf p "%s" (var_name id)
  | Etempvar (id, _) -> fprintf p "%s" (tname ctx id)
  | Ederef (a1, _) -> fprintf p "*%a" (expr ctx) (prec', a1)
  | Efield (Ederef (a1, _), f, _) -> fprintf p "%a->%s" (expr ctx) (16, a1) (gname f)
  | Efield (a1, f, _) -> fprintf p "%a.%s" (expr ctx) (prec', a1) (gname f)
  | Econst_int (n, (Tint _ as ty)) -> fprintf p "%s" (int_literal ty (camlint_of_coqint n))
  | Econst_int (n, ty) -> fprintf p "(%s) %ld" (name_type ty) (camlint_of_coqint n)
  | Econst_long (n, (Tlong _ as ty)) -> fprintf p "%s" (long_literal ty (camlint64_of_coqint n))
  | Econst_long (n, ty) -> fprintf p "(%s) %LdL" (name_type ty) (camlint64_of_coqint n)
  | Econst_float (f, _) -> fprintf p "%s" (double_literal (camlfloat_of_coqfloat f))
  | Econst_single (f, _) -> fprintf p "%s" (single_literal (camlfloat_of_coqfloat32 f))
  | Eunop (Oabsfloat, a1, _) -> fprintf p "__builtin_fabs(%a)" (expr ctx) (2, a1)
  | Eunop (Oneg, a1, _) when negative (drop_va_casts ctx a1)
                             || (match a1 with Eunop (Oneg, _, _) -> true | _ -> false) ->
      fprintf p "-(%a)" (expr ctx) (0, a1)
  | Eunop (op, a1, _) -> fprintf p "%s%a" (PrintCsyntax.name_unop op) (expr ctx) (prec', a1)
  | Eaddrof (a1, _) -> fprintf p "&%a" (expr ctx) (prec', a1)
  | Ebinop (op, a1, a2, _) ->
      let a1, a2 = match op with
        | Oeq | One | Olt | Ogt | Ole | Oge -> compared (drop_va_casts ctx a1) (drop_va_casts ctx a2)
        | _ -> (a1, a2) in
      let prec_of a pr = if clarify op (drop_va_casts ctx a) then 17 else pr in
      fprintf p "%a@ %s %a" (expr ctx) (prec_of a1 prec1, a1) (PrintCsyntax.name_binop op)
        (expr ctx) (prec_of a2 prec2, a2)
  | Ecast (a1, ty) -> fprintf p "(%s) %a" (name_type ty) (expr ctx) (prec', a1)
  | Esizeof (ty, _) -> fprintf p "sizeof(%s)" (name_type ty)
  | Ealignof (ty, _) -> fprintf p "_Alignof(%s)" (name_type ty)
  end;
  if paren then fprintf p ")@]" else fprintf p "@]"

(* Clight converts a value to the type it is stored, passed or returned
   at; C needs an explicit cast where a pointer is involved. *)
let needs_cast target source =
  let t = remove_attributes target and s = remove_attributes source in
  let same a b = type_eq (remove_attributes a) (remove_attributes b) in
  not (type_eq t s)
  && (match t, s with
      | Tpointer (a, _), Tarray (b, _, _) -> not (same a b)          (* decays *)
      | Tpointer (a, _), Tfunction _ -> not (same a s)
      | Tpointer (Tvoid, _), Tpointer (b, _) -> (match b with Tfunction _ -> true | _ -> false)
      | Tpointer (a, _), Tpointer (Tvoid, _) -> (match a with Tfunction _ -> true | _ -> false)
      | Tpointer _, _ -> true
      | (Tint _ | Tlong _), (Tpointer _ | Tarray _ | Tfunction _) -> true
      | _ -> false)

(* A function defined elsewhere is declared with the types of its C
   declaration (const), not Clight's; as a value it is cast to the pointer
   type the code expects. *)
let declared_elsewhere = function
  | Evar (g, Tfunction _) | Eaddrof (Evar (g, Tfunction _), _) ->
      (match Hashtbl.find_opt fundefs g with Some (External _) -> true | _ -> false)
  | _ -> false

let converted ctx target p e =
  let fn_value = match target with Tpointer (Tfunction _, _) -> declared_elsewhere e | _ -> false in
  if not (is_va_value ctx e) && (fn_value || needs_cast target (typeof e))
  then fprintf p "(%s) %a" (name_type target) (expr ctx) (14, e)
  else expr ctx p (2, e)

(* ** Statements *)

let callee_params e =
  match typeof e with
  | Tfunction (args, _, _) | Tpointer (Tfunction (args, _, _), _) -> args
  | _ -> []

let last_param ctx =
  match List.rev ctx.f.fn_params with (p, _) :: _ -> tname ctx p | [] -> "0"

let temp_type ctx id =
  match List.assoc_opt id ctx.f.fn_params with
  | Some t -> t
  | None -> (match List.assoc_opt id ctx.f.fn_temps with Some t -> t | None -> Tvoid)

let assign_to ctx p = function
  | Some id -> fprintf p "%s =@ " (tname ctx id)
  | None -> ()

let call ctx p (dst, callee, args) =
  match Option.bind (callee_name callee) va_arg_type, Option.bind (callee_name callee) Option.some, args with
  | Some ty, _, [a] ->
      fprintf p "@[<hv 2>%a__builtin_va_arg(%a, %s)@]" (assign_to ctx) dst (expr ctx) (2, strip_casts a) ty
  | None, Some "__builtin_va_start", [a] ->
      fprintf p "__builtin_va_start(%a, %s)" (expr ctx) (2, strip_casts a) (last_param ctx)
  | _ ->
      let targs = callee_params callee in
      let g = match callee with Evar (g, _) -> Some g | _ -> None in
      let arg p (i, a) =
        let va = is_va_value ctx a
                 || (match g with Some g -> Hashtbl.mem va_params (g, i) | None -> false) in
        match List.nth_opt targs i with
        | Some t when not va -> converted ctx t p a
        | _ -> expr ctx p (2, if va then strip_casts a else a) in
      let rec args_list i p = function
        | [] -> ()
        | a :: l -> if i > 0 then fprintf p ",@ "; arg p (i, a); args_list (i + 1) p l in
      let callee_text p () =
        match callee with
        | Evar (g, Tfunction ([], res, cc)) when cc.cc_unproto && args <> []
                                             && not (match Hashtbl.find_opt kr_args g with
                                                     | Some (Some _) -> true | _ -> false) ->
            (* Calls that disagree: each through a prototype of its own. *)
            let ty = Tpointer (Tfunction (promoted args, res, { cc with cc_unproto = false }), noattr) in
            fprintf p "((%s) %s)" (name_type ty) (gname g)
        | _ -> expr ctx p (16, callee) in
      fprintf p "@[<hv 2>%a%a(@[<hov 0>%a@])@]" (assign_to ctx) dst callee_text () (args_list 0) args

(* [*a], or [x] when [a] is [&x]. *)
let deref a =
  match a with
  | Eaddrof (x, _) -> x
  | _ -> Ederef (a, (match typeof a with Tpointer (t, _) -> t | _ -> Tvoid))

let builtin ctx p dst ef args =
  let plain p l = let rec go i p = function
                    | [] -> () | a :: l -> if i > 0 then fprintf p ",@ "; expr ctx p (2, a); go (i + 1) p l in
                  go 0 p l in
  match ef, args with
  | EF_vload _, [a] -> fprintf p "@[<hv 2>%a%a;@]" (assign_to ctx) dst (expr ctx) (2, deref a)
  | EF_vstore _, [a; v] -> fprintf p "@[<hv 2>%a =@ %a;@]" (expr ctx) (0, deref a) (expr ctx) (2, v)
  | EF_memcpy _, [d; s] when is_va_value ctx d || is_va_value ctx s ->
      fprintf p "__builtin_va_copy(%a, %a);" (expr ctx) (2, strip_casts d) (expr ctx) (2, strip_casts s)
  | EF_memcpy (sz, _), [d; s] ->
      fprintf p "__builtin_memcpy(%a, %a, %s);" (expr ctx) (2, d) (expr ctx) (2, s) (Z.to_string sz)
  | EF_annot_val _, [a] -> fprintf p "%a%a;" (assign_to ctx) dst (expr ctx) (2, a)
  | (EF_annot _ | EF_debug _ | EF_annot_val _), _ -> fprintf p ";"
  | EF_inline_asm (text, _, _), _ -> fprintf p "__asm__ volatile (%s);" (c_string text)
  | EF_malloc, _ -> fprintf p "@[<hv 2>%amalloc(%a);@]" (assign_to ctx) dst plain args
  | EF_free, _ -> fprintf p "free(%a);" plain args
  | (EF_external (name, _) | EF_builtin (name, _) | EF_runtime (name, _)), _ ->
      let name = match List.assoc_opt name builtin_renames with Some n -> n | None -> name in
      fprintf p "@[<hv 2>%a%s(@[<hov 0>%a@]);@]" (assign_to ctx) dst name plain args
  | (EF_vload _ | EF_vstore _ | EF_memcpy _), _ -> fprintf p ";"

let is_special_call = function
  | Scall (_, callee, _) ->
      (match callee_name callee with
       | Some n -> va_arg_type n <> None || n = "__builtin_va_start"
       | None -> false)
  | _ -> false

(* A loop step that a for statement can hold: assignments and calls. *)
let rec simple_step = function
  | Sskip | Sset _ | Sassign _ -> true
  | Scall _ as s -> not (is_special_call s)
  | Ssequence (s1, s2) -> simple_step s1 && simple_step s2
  | _ -> false

let fresh_label ctx = ctx.labels <- ctx.labels + 1; fresh (sprintf "c2r_continue_%d" ctx.labels)

(* Does [s] continue the loop around it? A loop inside [s] has its own. *)
let rec continues = function
  | Scontinue -> true
  | Ssequence (a, b) | Sifthenelse (_, a, b) -> continues a || continues b
  | Slabel (_, a) -> continues a
  | Sswitch (_, ls) ->
      let rec go = function LSnil -> false | LScons (_, s, rem) -> continues s || go rem in
      go ls
  | _ -> false

(* CompCert keeps case values modulo 2^32 or 2^64; a switch on a signed
   type needs them signed. *)
let case_value ty n =
  let s = Z.to_string n in
  match ty with
  | Tint (I32, Unsigned, _) -> s ^ "U"
  | Tint _ ->
      let v = Int64.of_string s in
      Int64.to_string (if v >= 0x80000000L then Int64.sub v 0x100000000L else v)
  | Tlong (Signed, _) ->
      (match Int64.of_string_opt s with
       | Some v -> long_literal ty v
       | None -> long_literal ty (Int64.of_string ("0u" ^ s)))
  | _ -> s ^ "UL"

(* ** Runs of zero stores: CompCert initializes a local array or struct
   ({0}) one element at a time; a long run is printed as one memset. *)

let size_of ty = Z.to_int (sizeof !ce ty)

let rec const_int = function
  | Econst_int (n, _) -> Some (Int32.to_int (camlint_of_coqint n))
  | Econst_long (n, _) -> Some (Int64.to_int (camlint64_of_coqint n))
  | Ecast (e, _) -> const_int e
  | _ -> None

let rec is_zero = function
  | Econst_float (f, _) -> camlint64_of_coqint (Floats.Float.to_bits f) = 0L
  | Econst_single (f, _) -> camlint_of_coqint (Floats.Float32.to_bits f) = 0l
  | Ecast (e, _) -> is_zero e
  | e -> const_int e = Some 0

(* An lvalue at a fixed place in a local variable: (variable, offset, size). *)
let rec place ctx lv =
  let at base k ty =
    match typeof base with
    | Tarray (elt, _, _) ->
        Option.map (fun (x, o, _) -> (x, o + k * size_of elt, size_of ty)) (place ctx base)
    | _ -> None in
  if (attr_of_type (typeof lv)).attr_volatile then None else
  match lv with
  | Evar (x, ty) when Hashtbl.mem ctx.vars x -> Some (x, 0, size_of ty)
  | Efield (a, f, ty) ->
      (match typeof a with
       | Tstruct (id, _) ->
           (match Maps.PTree.get id !ce with
            | Some co ->
                (match field_offset !ce f co.co_members with
                 | Errors.OK (fo, Full) ->
                     Option.map (fun (x, o, _) -> (x, o + Z.to_int fo, size_of ty)) (place ctx a)
                 | _ -> None)
            | None -> None)
       | Tunion _ -> Option.map (fun (x, o, _) -> (x, o, size_of ty)) (place ctx a)
       | _ -> None)
  | Ederef (Ebinop (Oadd, base, k, _), ty) ->
      (match const_int k with Some k -> at base k ty | None -> None)
  | Ederef (base, ty) -> at base 0 ty
  | _ -> None

let rec flatten = function
  | Ssequence (s1, s2) -> flatten s1 @ flatten s2
  | Sskip -> []
  | s -> [s]

type item = Stmt of statement | Memset of ident * int * int

let zero_runs ctx l =
  let zero_store = function
    | Sassign (lv, v) when is_zero v -> place ctx lv
    | _ -> None in
  let rec go acc = function
    | [] -> List.rev acc
    | s :: rest ->
        match zero_store s with
        | Some (x, o, n) ->
            (* Extend while the stores fill the bytes that follow. *)
            let rec extend count stop = function
              | s' :: rest' ->
                  (match zero_store s' with
                   | Some (x', o', n') when P.eq x x' && o' = stop -> extend (count + 1) (o' + n') rest'
                   | _ -> (count, stop, s' :: rest'))
              | [] -> (count, stop, []) in
            let (count, stop, rest') = extend 1 (o + n) rest in
            if count >= 16 then go (Memset (x, o, stop - o) :: acc) rest'
            else go (Stmt s :: acc) rest
        | None -> go (Stmt s :: acc) rest in
  go [] l

(* [cont]: where a continue goes, when it cannot be a C continue. *)
let rec stmt ctx cont p s =
  match s with
  | Sskip -> fprintf p ";"
  | Ssequence _ ->
      (match zero_runs ctx (flatten s) with
       | [] -> fprintf p ";"
       | items ->
           List.iteri (fun i it ->
             if i > 0 then fprintf p "@ ";
             match it with
             | Stmt s -> stmt ctx cont p s
             | Memset (x, 0, n) -> fprintf p "__builtin_memset(&%s, 0, %d);" (var_name x) n
             | Memset (x, o, n) -> fprintf p "__builtin_memset((char *) &%s + %d, 0, %d);" (var_name x) o n)
             items)
  | Sassign (e1, e2) ->
      fprintf p "@[<hv 2>%a =@ %a;@]" (expr ctx) (0, e1) (converted ctx (typeof e1)) e2
  | Sset (id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (tname ctx id) (converted ctx (temp_type ctx id)) e2
  | Scall (dst, e1, el) -> fprintf p "%a;" (call ctx) (dst, e1, el)
  | Sbuiltin (dst, ef, _, el) -> builtin ctx p dst ef el
  | Sifthenelse (e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]" (expr ctx) (0, e) (stmt ctx cont) s1
  | Sifthenelse (e, Sskip, s2) ->
      fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]" (expr ctx) (15, e) (stmt ctx cont) s2
  | Sifthenelse (e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
        (expr ctx) (0, e) (stmt ctx cont) s1 (stmt ctx cont) s2
  | Sloop (s1, Sskip) ->
      fprintf p "@[<v 2>while (1) {@ %a@;<0 -2>}@]" (stmt ctx None) s1
  | Sloop (s1, s2) when simple_step s2 ->
      fprintf p "@[<v 2>for (;; @[<hv 0>%a@]) {@ %a@;<0 -2>}@]" (step ctx) s2 (stmt ctx None) s1
  | Sloop (s1, s2) when not (continues s1) ->
      fprintf p "@[<v 2>while (1) {@ %a@ %a@;<0 -2>}@]" (stmt ctx None) s1 (stmt ctx None) s2
  | Sloop (s1, s2) ->
      let l = fresh_label ctx in
      fprintf p "@[<v 2>while (1) {@ %a@ %s: ;@ %a@;<0 -2>}@]" (stmt ctx (Some l)) s1 l (stmt ctx None) s2
  | Sbreak -> fprintf p "break;"
  | Scontinue -> (match cont with Some l -> fprintf p "goto %s;" l | None -> fprintf p "continue;")
  | Sswitch (e, cases) ->
      fprintf p "@[<v 2>switch (%a) {@ %a@;<0 -2>}@]" (expr ctx) (0, e) (switch_cases ctx cont (typeof e)) cases
  | Sreturn None -> fprintf p "return;"
  | Sreturn (Some e) -> fprintf p "return %a;" (converted ctx ctx.f.fn_return) e
  | Slabel (lbl, s1) -> fprintf p "%s:@ %a" (gname lbl) (stmt ctx cont) s1
  | Sgoto lbl -> fprintf p "goto %s;" (gname lbl)

and switch_cases ctx cont ty p = function
  | LSnil -> ()
  | LScons (lbl, s, rem) ->
      let label p = function None -> fprintf p "default" | Some n -> fprintf p "case %s" (case_value ty n) in
      fprintf p "@[<v 2>%a:@ %a@]" label lbl (stmt ctx cont) s;
      if rem <> LSnil then fprintf p "@ %a" (switch_cases ctx cont ty) rem

and step ctx p = function
  | Ssequence (Sskip, s) | Ssequence (s, Sskip) -> step ctx p s
  | Ssequence (s1, s2) -> fprintf p "%a,@ %a" (step ctx) s1 (step ctx) s2
  | Sset (id, e) -> fprintf p "%s = %a" (tname ctx id) (converted ctx (temp_type ctx id)) e
  | Sassign (e1, e2) -> fprintf p "%a = %a" (expr ctx) (0, e1) (converted ctx (typeof e1)) e2
  | Scall (dst, e1, el) -> call ctx p (dst, e1, el)
  | _ -> fprintf p "(void) 0"

(* ** Functions *)

let fun_hint name = Hashtbl.find_opt hints.funs name

let hint_parts = function
  | Some t -> (match unroll t with
               | C.TFun (r, ps, _, _) -> Some r, (match ps with Some l -> List.map snd l | None -> [])
               | _ -> None, [])
  | None -> None, []

let rec iter_expr fn e =
  fn e;
  match e with
  | Ederef (a, _) | Eaddrof (a, _) | Eunop (_, a, _) | Ecast (a, _) | Efield (a, _, _) -> iter_expr fn a
  | Ebinop (_, a, b, _) -> iter_expr fn a; iter_expr fn b
  | _ -> ()

let stmt_exprs s =
  match s with
  | Sassign (a, b) -> [a; b]
  | Sset (_, a) -> [a]
  | Scall (_, a, l) -> a :: l
  | Sbuiltin (_, _, _, l) -> l
  | Sifthenelse (a, _, _) | Sswitch (a, _) | Sreturn (Some a) -> [a]
  | _ -> []

(* Plain names for the parameters and temporaries, unused by the
   variables and globals the function refers to. *)
let name_temps ctx =
  let used = Hashtbl.create 17 in
  List.iter (fun (v, _) -> Hashtbl.replace used (gname v) ()) ctx.f.fn_vars;
  iter_stmt (fun s -> List.iter (iter_expr (function
    | Evar (x, _) -> Hashtbl.replace used (var_name x) ()
    | _ -> ())) (stmt_exprs s)) ctx.f.fn_body;
  Hashtbl.replace used ctx.fname ();
  let unused base =
    let rec pick n =
      let s = if n = 0 then base else sprintf "%s_%d" base n in
      if Hashtbl.mem used s then pick (n + 1) else s in
    let s = pick 0 in
    Hashtbl.replace used s ();
    s in
  let name t =
    let base = match atom_name t with Some s -> sanitize s | None -> sprintf "t%d" (P.to_int t) in
    Hashtbl.replace ctx.temps t (unused base) in
  List.iter (fun (t, _) -> name t) ctx.f.fn_params;
  List.iter (fun (t, _) -> name t) ctx.f.fn_temps

(* The variables the body reads, and the temporaries it sets. *)
let reads_writes f =
  let reads = Hashtbl.create 17 and writes = Hashtbl.create 17 in
  iter_stmt (fun s ->
    List.iter (iter_expr (function
      | Etempvar (x, _) | Evar (x, _) -> Hashtbl.replace reads x ()
      | _ -> ())) (stmt_exprs s);
    match s with
    | Sset (x, _) | Scall (Some x, _, _) | Sbuiltin (Some x, _, _, _) -> Hashtbl.replace writes x ()
    | _ -> ()) f.fn_body;
  reads, writes

let static_prefix id = if C2C.atom_is_static id then "static " else ""

(* The C AST does not keep noreturn; the C library's functions are known. *)
let noreturn_prefix name =
  if List.mem name ["exit"; "_exit"; "_Exit"; "quick_exit"; "abort"; "longjmp"; "siglongjmp";
                       "thrd_exit"; "pthread_exit"; "__assert_fail"; "__assert_perror_fail";
                       "__assert"; "err"; "errx"; "verr"; "verrx"; "__stack_chk_fail"]
  then "__attribute__((noreturn)) " else ""

let print_function p id f =
  let ctx = fctx_of id f in
  name_temps ctx;
  let reads, writes = reads_writes f in
  let hres, hparams = hint_parts (fun_hint ctx.fname) in
  let params = List.mapi (fun i (x, t) ->
    if Hashtbl.mem va_params (id, i) then "__builtin_va_list " ^ tname ctx x
    else cdecl ?hint:(List.nth_opt hparams i) (tname ctx x) t) f.fn_params in
  let header = cdecl ?hint:hres (sprintf "%s(%s)" ctx.fname (param_list f.fn_callconv params)) f.fn_return in
  fprintf p "%s%s%s@ " (static_prefix id) (noreturn_prefix ctx.fname) header;
  fprintf p "@[<v 2>{@ ";
  let decl ~align x name t =
    if Hashtbl.mem va_vars (id, x) then "__builtin_va_list " ^ name
    else cdecl ~align ?hint:(local_hint ctx x) name t in
  (* Variables the body never mentions are left out; parameters and
     temporaries it never reads are read once with (void), as C code
     does to quiet compilers, a statement CompCert drops. *)
  let mentioned x = Hashtbl.mem reads x || Hashtbl.mem writes x in
  List.iter (fun (x, t) -> if mentioned x then fprintf p "%s;@ " (decl ~align:true x (gname x) t)) f.fn_vars;
  List.iter (fun (x, t) -> if mentioned x then fprintf p "%s;@ " (decl ~align:false x (tname ctx x) t)) f.fn_temps;
  List.iter (fun (x, _) -> if not (Hashtbl.mem reads x) then fprintf p "(void) %s;@ " (tname ctx x))
    (f.fn_params @ List.filter (fun (x, _) -> Hashtbl.mem writes x) f.fn_temps);
  stmt ctx None p f.fn_body;
  fprintf p "@;<0 -2>}@]@ @ "

let fun_decl ?(exact = false) id ty =
  let name = gname id in
  let va i = Hashtbl.mem va_params (id, i) in
  noreturn_prefix name ^ cdecl ~exact ~va ?hint:(fun_hint name) name ty

(* ** Global variables: the initializer rebuilt from its bytes *)

type image = { bytes: Bytes.t; relocs: (int, ident * int64) Hashtbl.t }

let image_of size il =
  let b = Bytes.make size '\000' and r = Hashtbl.create 4 in
  let pos = ref 0 in
  let put n v =
    for k = 0 to n - 1 do
      if !pos + k < size then
        Bytes.set b (!pos + k)
          (Char.chr (Int64.to_int (Int64.logand (Int64.shift_right_logical v (8 * k)) 0xFFL)))
    done;
    pos := !pos + n in
  List.iter (function
    | Init_int8 n -> put 1 (Int64.of_int32 (camlint_of_coqint n))
    | Init_int16 n -> put 2 (Int64.of_int32 (camlint_of_coqint n))
    | Init_int32 n -> put 4 (Int64.of_int32 (camlint_of_coqint n))
    | Init_int64 n -> put 8 (camlint64_of_coqint n)
    | Init_float32 f -> put 4 (Int64.of_int32 (camlint_of_coqint (Floats.Float32.to_bits f)))
    | Init_float64 f -> put 8 (camlint64_of_coqint (Floats.Float.to_bits f))
    | Init_space z -> pos := !pos + max 0 (Z.to_int z)
    | Init_addrof (s, o) -> Hashtbl.replace r !pos (s, camlint64_of_ptrofs o); pos := !pos + 8) il;
  { bytes = b; relocs = r }

let get img ofs n =
  let v = ref 0L in
  for k = n - 1 downto 0 do
    let c = if ofs + k < Bytes.length img.bytes then Char.code (Bytes.get img.bytes (ofs + k)) else 0 in
    v := Int64.logor (Int64.shift_left !v 8) (Int64.of_int c)
  done;
  !v

let sext v bits = if bits >= 64 then v else Int64.shift_right (Int64.shift_left v (64 - bits)) (64 - bits)

let zero img ofs len =
  let rec go i = i >= ofs + len || i >= Bytes.length img.bytes
                 || (Bytes.get img.bytes i = '\000' && not (Hashtbl.mem img.relocs i) && go (i + 1)) in
  go ofs

type itree = Leaf of string | Node of itree list | Field of string * itree

let reloc_text ty (s, o) =
  if o = 0L then sprintf "(%s) &%s" (name_type ty) (gname s)
  else sprintf "(%s) ((char *) &%s + %Ld)" (name_type ty) (gname s) o

let text_like img ofs n =
  let ok = ref true in
  for i = ofs to ofs + n - 1 do
    match Char.chr (Int64.to_int (get img i 1)) with
    | ' '..'~' | '\n' | '\t' | '\r' | '\000' -> ()
    | _ -> ok := false
  done;
  !ok

let rec tree ~as_string img ty ofs =
  match ty with
  | Tint (IBool, _, _) -> Leaf (if get img ofs 1 <> 0L then "1" else "0")
  | Tint (sz, sg, _) ->
      let n = match sz with I8 -> 1 | I16 -> 2 | _ -> 4 in
      (match Hashtbl.find_opt img.relocs ofs with
       | Some r -> Leaf (reloc_text ty r)
       | None ->
           let v = get img ofs n in
           Leaf (match sz, sg with
                 | I32, Unsigned -> sprintf "%LuU" v
                 | I8, Unsigned when v > 127L -> sprintf "(char) %Lu" v
                 | _, Signed -> int_literal ty (Int64.to_int32 (sext v (8 * n)))
                 | _, Unsigned -> sprintf "%Lu" v))
  | Tlong _ ->
      (match Hashtbl.find_opt img.relocs ofs with
       | Some r -> Leaf (reloc_text ty r)
       | None -> Leaf (long_literal ty (get img ofs 8)))
  | Tfloat (F32, _) -> Leaf (single_literal (Int32.float_of_bits (Int64.to_int32 (get img ofs 4))))
  | Tfloat (F64, _) -> Leaf (double_literal (Int64.float_of_bits (get img ofs 8)))
  | Tpointer _ ->
      (match Hashtbl.find_opt img.relocs ofs with
       | Some r -> Leaf (reloc_text ty r)
       | None -> let v = get img ofs 8 in
                 Leaf (if v = 0L then "0" else sprintf "(%s) %LuUL" (name_type ty) v))
  | Tarray (t, n, _) ->
      let n = Z.to_int n and es = size_of t in
      let chars = (match t with Tint (I8, _, _) -> true | _ -> false) && zero_relocs img ofs (n * es) in
      if chars && not (zero img ofs n) && (as_string || text_like img ofs n) then begin
        let last = ref (-1) in
        for i = 0 to n - 1 do if get img (ofs + i) 1 <> 0L then last := i done;
        Leaf (c_string (Bytes.sub_string img.bytes ofs (!last + 1)))
      end else begin
        let elems = List.init n (fun i -> (zero img (ofs + i * es) es, i)) in
        let rec trim = function (true, _) :: l -> trim l | l -> l in
        let kept = List.rev (trim (List.rev elems)) in
        Node (List.map (fun (_, i) -> tree ~as_string:false img t (ofs + i * es)) kept)
      end
  | Tstruct (id, _) ->
      (match Maps.PTree.get id !ce with
       | None -> Node []
       | Some co ->
           Node (List.filter_map (fun m ->
             match m with
             | Member_bitfield (_, _, _, _, _, true) -> None
             | _ ->
               let f = name_member m in
               match field_offset !ce f co.co_members with
               | Errors.OK (fo, Full) ->
                   let o = ofs + Z.to_int fo and t = type_member m in
                   if zero img o (size_of t) then None
                   else Some (Field (gname f, tree ~as_string:false img t o))
               | Errors.OK (fo, Bits (sz, sg, pos, width)) ->
                   let n = match sz with I8 | IBool -> 1 | I16 -> 2 | I32 -> 4 in
                   let width = Z.to_int width in
                   let v = Int64.shift_right_logical (get img (ofs + Z.to_int fo) n) (Z.to_int pos) in
                   let v = Int64.logand v (Int64.pred (Int64.shift_left 1L width)) in
                   let v = if sg = Signed then sext v width else v in
                   if v = 0L then None else Some (Field (gname f, Leaf (Int64.to_string v)))
               | Errors.Error _ -> None) co.co_members))
  | Tunion (id, _) ->
      (match Maps.PTree.get id !ce with
       | None -> Node []
       | Some co ->
           let total = size_of ty in
           if zero img ofs total then Node []
           else begin
             let extent = ref 0 in
             for i = 0 to total - 1 do
               if not (zero img (ofs + i) 1) then extent := i + 1
             done;
             let plain = List.filter_map (function Member_plain (f, t) -> Some (f, t) | _ -> None) co.co_members in
             match List.find_opt (fun (_, t) -> size_of t >= !extent) plain, plain with
             | Some (f, t), _ | None, (f, t) :: _ -> Node [Field (gname f, tree ~as_string:false img t ofs)]
             | None, [] -> Node []
           end)
  | Tvoid | Tfunction _ -> Leaf "0"

and zero_relocs img ofs len =
  let rec go i = i >= ofs + len || (not (Hashtbl.mem img.relocs i) && go (i + 1)) in
  go ofs

let rec print_tree p = function
  | Leaf s -> fprintf p "%s" s
  | Node [] -> fprintf p "{0}"
  | Node l ->
      fprintf p "@[<hov 2>{ ";
      List.iteri (fun i t -> if i > 0 then fprintf p ",@ "; print_tree p t) l;
      fprintf p " }@]"
  | Field (f, t) -> fprintf p ".%s = %a" f print_tree t

let var_decl ?(unsized = false) id v =
  let name = gname id in
  (* No const: Clight's types have none, so the code that uses the
     variable would discard it. *)
  let name = (if v.gvar_volatile then "volatile " else "") ^ name in
  let align = match C2C.atom_alignof id with
    | Some a when a > Z.to_int (alignof !ce v.gvar_info) -> aligned (Int64.of_int a) ^ " "
    | _ -> "" in
  let hint = Option.bind (atom_name id) (Hashtbl.find_opt hints.globals) in
  align ^ (match v.gvar_info with
           | Tarray (t, n, _) when unsized && Z.to_int n = 0 ->
               let hint' = match Option.map unroll hint with Some (C.TArray (t', _, _)) -> Some t' | _ -> None in
               cdecl ~align:true ?hint:hint' (name ^ "[]") t
           | ty -> cdecl ~align:true ?hint name ty)

let print_globvar p id v =
  match v.gvar_init with
  | [] -> fprintf p "extern %s;@ @ " (var_decl ~unsized:true id v)
  | [Init_space _] -> fprintf p "%s%s;@ @ " (static_prefix id) (var_decl id v)
  | il ->
      let img = image_of (max (size_of v.gvar_info) (Z.to_int (init_data_list_size il))) il in
      let as_string = C2C.atom_literal id = C2C.String_literal in
      fprintf p "@[<hov 2>%s%s =@ %a;@]@ @ " (static_prefix id) (var_decl id v)
        print_tree (tree ~as_string img v.gvar_info 0)

(* ** The program *)

let rec tags_of acc ty =
  match ty with
  | Tstruct (id, _) -> (id, Struct) :: acc
  | Tunion (id, _) -> (id, Union) :: acc
  | Tpointer (t, _) | Tarray (t, _, _) -> tags_of acc t
  | Tfunction (args, res, _) -> List.fold_left tags_of (tags_of acc res) args
  | _ -> acc

(* Every struct and union a type in the program mentions, so that each
   is declared once at file scope. *)
let all_tags prog =
  let acc = ref [] in
  let add ty = acc := tags_of !acc ty in
  List.iter (fun (Composite (id, su, ms, _)) ->
    acc := (id, su) :: !acc; List.iter (fun m -> add (type_member m)) ms) prog.prog_types;
  List.iter (fun (_, gd) ->
    match gd with
    | Gvar v -> add v.gvar_info
    | Gfun (External (_, args, res, _)) -> List.iter add args; add res
    | Gfun (Internal f) ->
        add (type_of_function f);
        List.iter (fun (_, t) -> add t) (f.fn_vars @ f.fn_temps);
        iter_stmt (fun s -> List.iter (iter_expr (fun e ->
          add (typeof e);
          match e with Ecast (_, t) | Esizeof (t, _) | Ealignof (t, _) -> add t | _ -> ()))
          (stmt_exprs s)) f.fn_body) prog.prog_defs;
  let seen = Hashtbl.create 17 in
  List.filter (fun (id, _) -> if Hashtbl.mem seen id then false else (Hashtbl.replace seen id (); true))
    (List.rev !acc)

let print_composite p (Composite (id, su, ms, a)) =
  let kw = match su with Struct -> "struct" | Union -> "union" in
  let align = match a.attr_alignas with
    | Some l -> sprintf " __attribute__((aligned(%Ld)))" (Int64.shift_left 1L (N.to_int l))
    | None -> "" in
  fprintf p "@[<v 2>%s%s %s {" kw align (gname id);
  let n = List.length ms in
  List.iteri (fun i m ->
    match m with
    | Member_plain (f, Tarray (t, z, _)) when i = n - 1 && Z.to_int z = 0 ->
        fprintf p "@ %s;" (cdecl ~align:true (gname f ^ "[]") t)
    | Member_plain (f, t) -> fprintf p "@ %s;" (cdecl ~align:true (gname f) t)
    | Member_bitfield (f, sz, sg, at, w, pad) ->
        fprintf p "@ %s%s%s : %s;" (PrintCsyntax.name_inttype sz sg) (attrs false at)
          (optid (if pad then "" else gname f)) (Z.to_string w)) ms;
  fprintf p "@;<0 -2>};@]@ @ "

(* The externals not to declare: clang's builtins and CompCert's runtime,
   unless the code still calls them. *)
let compcert_internal name =
  String.starts_with ~prefix:"__builtin_" name || String.starts_with ~prefix:"__compcert_" name

let print_program (cast: C.program) p prog =
  Hashtbl.reset taken; Hashtbl.reset global_names; Hashtbl.reset fundefs;
  read_hints cast;
  ce := prog.prog_comp_env;
  List.iter (fun (id, gd) -> match gd with Gfun fd -> Hashtbl.replace fundefs id fd | _ -> ()) prog.prog_defs;
  infer_va prog;
  (* Globals the code refers to, other than va_arg and va_start. *)
  let called = Hashtbl.create 101 in
  List.iter (fun (_, gd) ->
    match gd with
    | Gfun (Internal f) ->
        iter_stmt (fun s ->
          if not (is_special_call s) then
            List.iter (iter_expr (function Evar (x, _) -> Hashtbl.replace called x () | _ -> ()))
              (stmt_exprs s)) f.fn_body
    | _ -> ()) prog.prog_defs;
  Hashtbl.reset kr_args;
  List.iter (fun (_, gd) ->
    match gd with
    | Gfun (Internal f) ->
        iter_stmt (function
          | Scall (_, Evar (g, _), args) ->
              let tys = promoted args in
              Hashtbl.replace kr_args g
                (match Hashtbl.find_opt kr_args g with
                 | None -> Some tys
                 | Some (Some tys') when tys' = tys -> Some tys
                 | Some _ -> None)
          | _ -> ()) f.fn_body
    | _ -> ()) prog.prog_defs;
  (* Variables that initializers point to: declared before any definition. *)
  let pointed = Hashtbl.create 17 in
  List.iter (fun (_, gd) ->
    match gd with
    | Gvar v -> List.iter (function Init_addrof (s, _) -> Hashtbl.replace pointed s () | _ -> ()) v.gvar_init
    | _ -> ()) prog.prog_defs;
  (* clang checks declarations of fprintf and the like against FILE. *)
  let rec file_struct t =
    match t with
    | C.TNamed (tid, _) when tid.C.name = "FILE" ->
        (match unroll t with C.TStruct (sid, _) -> Some sid.C.name | _ -> None)
    | C.TPtr (t, _) | C.TArray (t, _, _) -> file_struct t
    | C.TFun (r, ps, _, _) ->
        List.fold_left (fun acc (_, t) -> if acc = None then file_struct t else acc)
          (file_struct r) (Option.value ps ~default:[])
    | _ -> None in
  let file = List.find_map (fun (id, gd) ->
    match gd with Gfun (External _) -> Option.bind (fun_hint (gname id)) file_struct | _ -> None) prog.prog_defs in
  let tags = all_tags prog in
  let printed = ref (tags <> []) in
  fprintf p "@[<v 0>";
  (* String literals are named arrays, so printf(s) has a format that is
     not a literal. *)
  if List.exists (fun (id, gd) ->
       match gd, atom_name id with
       | Gfun (External _), Some n -> List.mem n ["printf"; "fprintf"; "dprintf"; "sprintf"; "snprintf"; "syslog"]
       | _ -> false) prog.prog_defs
  then fprintf p "#pragma GCC diagnostic ignored \"-Wformat-security\"@ @ ";
  List.iter (fun (id, su) ->
    fprintf p "%s %s;@ " (match su with Struct -> "struct" | Union -> "union") (gname id)) tags;
  Option.iter (fun s -> fprintf p "typedef struct %s FILE;@ " (gname (intern_string s))) file;
  fprintf p "@ ";
  List.iter (print_composite p) prog.prog_types;
  List.iter (fun (id, gd) ->
    match gd with
    | Gvar v when Hashtbl.mem pointed id && v.gvar_init <> [] ->
        fprintf p "%s%s;@ " (if C2C.atom_is_static id then "static " else "extern ") (var_decl id v)
    | Gfun (Internal f) -> fprintf p "%s%s;@ " (static_prefix id) (fun_decl id (type_of_function f))
    | Gfun (External ((EF_external _ | EF_runtime _ | EF_malloc | EF_free), args, res, cc)) ->
        let name = gname id in
        let ty =
          match args, Hashtbl.find_opt kr_args id with
          | [], Some (Some tys) when cc.cc_unproto -> Tfunction (tys, res, { cc with cc_unproto = false })
          | _ -> Tfunction (args, res, cc) in
        if not (compcert_internal name) || (Hashtbl.mem called id && va_arg_type name = None) then begin
          fprintf p "extern %s;@ " (fun_decl ~exact:true id ty);
          printed := true
        end
    | _ -> ()) prog.prog_defs;
  fprintf p "@ ";
  List.iter (fun (id, gd) ->
    match gd with
    | Gvar v when is_func_atom id && not (Hashtbl.mem pointed id) -> ()
    | Gvar v -> print_globvar p id v; printed := true
    | Gfun (Internal f) -> print_function p id f; printed := true
    | Gfun (External _) -> ()) prog.prog_defs;
  (* ISO C wants at least one declaration in a file. *)
  if not !printed then fprintf p "typedef int c2r_empty_file;@ ";
  fprintf p "@]@."

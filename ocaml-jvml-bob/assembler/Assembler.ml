(* This program reads in a textual representation of a class_decl and
   compiles it to a .class file. *)

module C   = Ocaml_jvml.Compile
module CFO = Ocaml_jvml.ClassfileOutput
module U   = Ocaml_jvml.Util
module JT  = Ocaml_jvml.Jvmtype
module AP  = Assembler_parser
module CP  = Ocaml_jvml.Constpool

type cpaentry =
  | CPAE_static_method of JT.jref_type * string * JT.methodsig * string * string * string
  | CPAE_static_field of JT.jclass * string * JT.jtype
  | CPAE_instantiable_class of JT.jref_type
  | CPAE_instance_field of JT.jclass * string * JT.jtype
  | CPAE_instance_method of JT.jref_type * string * JT.methodsig * string * string * string
  | CPAE_instance_special_method of JT.jref_type * string * JT.methodsig * string * string * string
  | CPAE_interface_method of JT.jclass * string * JT.methodsig * string * string * string
  | CPAE_classref of JT.jref_type

type res_class_attr =
    { cl_prooftable : (string * string * string) list
    ; cl_cpa        : cpaentry list
    }

type res_method_attr =
    { m_requires : string option
    ; m_ensures  : string option
    ; m_exsures  : string option
    ; m_grants   : string option
    }

type res_code_attr = (Ocaml_jvml.Label.label * string) list

let parse_requires input ma =
  let pos = input#pos in
  let s   = Assembler_parser.read_string input in
    match ma.m_requires with
      | None -> {ma with m_requires = Some s}
      | Some _ -> raise (Assembler_parser.Parse_error ("Duplicate 'requires'", pos))

let parse_ensures input ma =
  let pos = input#pos in
  let s   = Assembler_parser.read_string input in
    match ma.m_ensures with
      | None -> {ma with m_ensures = Some s}
      | Some _ -> raise (Assembler_parser.Parse_error ("Duplicate 'ensures'", pos))

let parse_exsures input ma =
  let pos = input#pos in
  let s   = Assembler_parser.read_string input in
    match ma.m_exsures with
      | None -> {ma with m_exsures = Some s}
      | Some _ -> raise (Assembler_parser.Parse_error ("Duplicate 'exsures'", pos))

let parse_grants input ma =
  let pos = input#pos in
  let s   = Assembler_parser.read_string input in
    match ma.m_grants with
      | None -> {ma with m_grants = Some s}
      | Some _ -> raise (Assembler_parser.Parse_error ("Duplicate 'grants'", pos))

let method_attr_parsers =
  let t = Hashtbl.create 3 in
    Hashtbl.add t "requires" parse_requires;
    Hashtbl.add t "ensures" parse_ensures;
    Hashtbl.add t "exsures" parse_exsures;
    Hashtbl.add t "grants" parse_grants;
    t

let parse_code_annotation input parse_label annots =
  let pos   = input#pos in
  let label = AP.read_word input in
  let annot = AP.read_string input in
    (parse_label label pos, annot)::annots

let code_attr_parsers =
  let t = Hashtbl.create 1 in
    Hashtbl.add t "proof_annotation" parse_code_annotation;
    t

let parse_proof input ca =
  let p     = AP.read_string input in
  let q     = AP.read_string input in
  let proof = AP.read_string input in
    {ca with cl_prooftable = (p,q,proof)::ca.cl_prooftable}

let parse_cpa input ca =
  let pos = input#pos in
  let cpae = (match AP.read_word input with
		| "static_method" ->
		    let (class_name, meth_name, msig) = AP.read_method_name input in
		    let requires                      = AP.read_string input in
		    let ensures                       = AP.read_string input in
		    let exsures                       = AP.read_string input in
		      CPAE_static_method (class_name, meth_name, msig, requires, ensures, exsures)
		| "static_field" ->
		    let (clsnm, fnm, ty) = AP.read_field_name input in
		      CPAE_static_field (clsnm, fnm, ty)
		| "instantiable_class" ->
		    let clsnm = AP.read_reftype input in
		      CPAE_instantiable_class clsnm
		| "instance_field" ->
		    let (clsnm, fnm, ty) = AP.read_field_name input in
		      CPAE_instance_field (clsnm, fnm, ty)
		| "instance_method" ->
		    let (clsnm, mnm, msig)            = AP.read_method_name input in
		    let requires                      = AP.read_string input in
		    let ensures                       = AP.read_string input in
		    let exsures                       = AP.read_string input in
		      CPAE_instance_method (clsnm, mnm, msig, requires, ensures, exsures)
		| "instance_special_method" ->
		    let (clsnm, mnm, msig)            = AP.read_method_name input in
		    let requires                      = AP.read_string input in
		    let ensures                       = AP.read_string input in
		    let exsures                       = AP.read_string input in
		      CPAE_instance_special_method (clsnm, mnm, msig, requires, ensures, exsures)
		| "interface_method" ->
		    let (clsnm, mnm, msig)            = AP.read_imethod_name input in
		    let requires                      = AP.read_string input in
		    let ensures                       = AP.read_string input in
		    let exsures                       = AP.read_string input in
		      CPAE_interface_method (clsnm, mnm, msig, requires, ensures, exsures)
		| "class" ->
		    let clsnm = AP.read_reftype input in
		      CPAE_classref clsnm
		| w ->
		    raise (AP.Parse_error ("Unknown linkinfo type: " ^ w, pos))) in
    {ca with cl_cpa = cpae::ca.cl_cpa}

let class_attr_parsers =
  let t = Hashtbl.create 2 in
    Hashtbl.add t "linkinfo" parse_cpa;
    Hashtbl.add t "proof" parse_proof;
    t

let res_parsers =
  { AP.empty_field_attribute     = ()
  ; AP.empty_method_attribute    = { m_requires = None; m_ensures = None; m_exsures = None; m_grants = None }
  ; AP.empty_code_attribute      = ([] : (Ocaml_jvml.Label.label * string) list)
  ; AP.empty_class_attribute     = { cl_prooftable = []; cl_cpa = [] }
  ; AP.parser_custom_attr_field  = Hashtbl.create 0
  ; AP.parser_custom_attr_method = method_attr_parsers
  ; AP.parser_custom_attr_code   = code_attr_parsers
  ; AP.parser_custom_attr_class  = class_attr_parsers
  }

let res_compile_method_attr ma cp_builder =
  let ensures  = Option.default "TT" ma.m_ensures in
  let requires = Option.default "TT" ma.m_requires in
  let exsures  = Option.default "TT" ma.m_exsures in
  let attrs    =  [("uk.ac.ed.inf.request.Spec", String.concat " " [requires;ensures;exsures])] in
    (match ma.m_grants with
       | None -> attrs
       | Some s -> ("uk.ac.ed.inf.request.Grants", s)::attrs)

let res_compile_code_attr annots cp_builder label_map =
  let parts = List.map (fun (label, annot) -> (string_of_int (Hashtbl.find label_map label)) ^ ";" ^ annot) annots in
    [("uk.ac.ed.inf.request.Certificate", String.concat ";" parts)]

let res_compile_class_attr ca cp_builder =
  let string_of_index idx = string_of_int (CP.index_to_int idx) in
  let compile_cpae cpae = match cpae with
    | CPAE_static_method (clsnm, mnm, msig, requires, ensures, exsures) ->
	string_of_index (CP.add_method_ref cp_builder (clsnm, mnm, msig)) ^ ";sm" ^ String.concat " " [requires;ensures;exsures]
    | CPAE_instance_method (clsnm, mnm, msig, requires, ensures, exsures) ->
	string_of_index (CP.add_method_ref cp_builder (clsnm, mnm, msig)) ^ ";im" ^ String.concat " " [requires;ensures;exsures]
    | CPAE_instance_special_method (clsnm, mnm, msig, requires, ensures, exsures) ->
	string_of_index (CP.add_method_ref cp_builder (clsnm, mnm, msig)) ^ ";is" ^ String.concat " " [requires;ensures;exsures]
    | CPAE_interface_method (clsnm, mnm, msig, requires, ensures, exsures) ->
	string_of_index (CP.add_imethod_ref cp_builder (clsnm, mnm, msig)) ^ ";fm" ^ String.concat " " [requires;ensures;exsures]
    | CPAE_instance_field (clsnm, fnm, ty) ->
	string_of_index (CP.add_field_ref cp_builder (clsnm,fnm,ty)) ^ ";if"
    | CPAE_static_field (clsnm, fnm, ty) ->
	string_of_index (CP.add_field_ref cp_builder (clsnm,fnm,ty)) ^ ";sf"
    | CPAE_instantiable_class clsnm ->
	string_of_index (CP.add_class cp_builder clsnm) ^ ";ic"
    | CPAE_classref clsnm ->
	string_of_index (CP.add_class cp_builder clsnm) ^ ";cr"
  in
    [ ("uk.ac.ed.inf.request.ConstantPoolAdditional", String.concat ";" (List.map compile_cpae ca.cl_cpa))
    ; ("uk.ac.ed.inf.request.ProofTable",             String.concat ";" (List.map (fun (p,q,prf) -> p ^ " " ^ q ^ ";" ^ prf) ca.cl_prooftable))
    ]

let res_compilers =
  { C.compile_field_attribute  = (fun () _ -> [])
  ; C.compile_method_attribute = res_compile_method_attr
  ; C.compile_code_attribute   = res_compile_code_attr
  ; C.compile_class_attribute  = res_compile_class_attr
  }

let _ =
  let input_file  = Sys.argv.(1) in
  let output_file = if Filename.check_suffix input_file ".j" then Filename.chop_suffix input_file ".j" ^ ".class" else input_file ^ ".class" in
    (try
       let lexbuf = Lexing.from_channel (open_in input_file) in
       let _      = lexbuf.Lexing.lex_curr_p <- {Lexing.pos_fname = "stdin"; Lexing.pos_lnum=1; Lexing.pos_bol=0; Lexing.pos_cnum=0} in
       let input  = (U.lookahead_lexer Assembler_lexer.token lexbuf) in
       let cd     = Assembler_parser.read input res_parsers in
       let cf     = C.compile cd res_compilers in
	 CFO.write_classfile (IO.output_channel (open_out output_file)) cf
     with
       | Assembler_parser.Parse_error (message, (start_pos, end_pos)) ->
	   Printf.fprintf stderr "Parse error: %s:%d: %s\n" start_pos.Lexing.pos_fname start_pos.Lexing.pos_lnum message;
	   exit 1)


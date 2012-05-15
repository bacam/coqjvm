(* FIXME TODO:
   - inner classes

   Additional directives to add:
   Methods:
   - requires
   - ensures
   - exsures
   Code:
   - invariant
   Class
   - proof
   - link information
*)

open Ocaml_jvml

module CD = Classdecl
module JT = Jvmtype
module AF = AccessFlags
module BC = Bytecode

type token =
  | DIRECTIVE of string
  | WORD of string
  | STRINGLIT of string
  | NEWLINE
  | EOF

type token_parser =
    < tok : token; advance : unit -> unit; pos : Lexing.position * Lexing.position >

type ('f,'m,'c,'cl) custom_attr_parsers =
    { empty_field_attribute   : 'f
    ; empty_method_attribute  : 'm
    ; empty_code_attribute    : 'c
    ; empty_class_attribute   : 'cl
    ; parser_custom_attr_field  : (string, token_parser -> 'f -> 'f) Hashtbl.t
    ; parser_custom_attr_method : (string, token_parser -> 'm -> 'm) Hashtbl.t
    ; parser_custom_attr_code   : (string, token_parser -> (string -> Lexing.position * Lexing.position -> Label.label) -> 'c -> 'c) Hashtbl.t
    ; parser_custom_attr_class  : (string, token_parser -> 'cl -> 'cl) Hashtbl.t
    }

let null_custom_attr_parsers =
  { empty_field_attribute = ()
  ; empty_method_attribute = ()
  ; empty_code_attribute = ()
  ; empty_class_attribute = ()
  ; parser_custom_attr_field = Hashtbl.create 0
  ; parser_custom_attr_method = Hashtbl.create 0
  ; parser_custom_attr_code   = Hashtbl.create 0
  ; parser_custom_attr_class  = Hashtbl.create 0
  }

exception Parse_error of string * (Lexing.position * Lexing.position)

let read_by_fallible ~reader ~error_message input = match input#tok with
  | WORD s ->
      let x = try reader s with Failure _ -> raise (Parse_error (error_message, input#pos)) in
	input#advance ();
	x
  | _ ->
      raise (Parse_error (error_message, input#pos))

let read_int input =
  read_by_fallible ~reader:int_of_string ~error_message:"expecting integer" input

let read_int32 input =
  read_by_fallible ~reader:Int32.of_string ~error_message:"expecting 32-bit integer" input

let read_int64 input =
  read_by_fallible ~reader:Int64.of_string ~error_message:"expecting 64-bit integer" input

let read_double input =
  read_by_fallible ~reader:float_of_string ~error_message:"expecting double" input

let read_newline input = match input#tok with
  | NEWLINE -> input#advance ()
  | EOF     -> ()
  | t       -> raise (Parse_error ("expecting newline", input#pos))

let read_directive d input = match input#tok with
  | DIRECTIVE s when s = d -> input#advance ()
  | _                      -> raise (Parse_error ("expecting ." ^ d, input#pos))

let read_classname input = match input#tok with
  | WORD s ->
      (match JT.class_of_string s with
	 | None       -> raise (Parse_error ("bad class name", input#pos))
	 | Some clsnm -> input#advance (); clsnm)
  | _ ->
      raise (Parse_error ("bad class name", input#pos))

let read_methodsig input = match input#tok with
  | WORD s ->
      (match JT.methodsig_of_string s with
	 | None       -> raise (Parse_error ("bad method signature", input#pos))
	 | Some clsnm -> input#advance (); clsnm)
  | _ ->
      raise (Parse_error ("bad method signature", input#pos))

let read_string input = match input#tok with
  | STRINGLIT s -> input#advance (); s
  | t           -> raise (Parse_error ("expecting string literal", input#pos))

let read_word input = match input#tok with
  | WORD w -> input#advance (); w
  | _      -> raise (Parse_error ("expecting bare word", input#pos))

let read_specific_word w' input = match input#tok with
  | WORD w when w = w' -> input#advance ()
  | _                  -> raise (Parse_error ("expecting '"^w'^"'", input#pos))

let peek_word w' input = match input#tok with
  | WORD w when w = w' -> true
  | _                  -> false

let read_jtype input = match input#tok with
  | WORD w ->
      (match JT.type_of_string w with
	 | None       -> raise (Parse_error ("bad type", input#pos))
	 | Some jtype -> input#advance (); jtype)
  | t      -> raise (Parse_error ("bad type", input#pos))

let read_reftype input = match input#tok with
  | WORD w ->
      (match JT.reftype_of_string w with
	 | None       -> raise (Parse_error ("bad reference type", input#pos))
	 | Some jtype -> input#advance (); jtype)
  | t      -> raise (Parse_error ("bad reference type", input#pos))

let read_field_name input =
  let clsnm = read_classname input in
  let fnm   = read_word input in
  let ty    = read_jtype input in
    (clsnm, fnm, ty)

let read_imethod_name input =
  let clsnm = read_classname input in
  let mnm   = read_word input in
  let msig  = read_methodsig input in
    (clsnm, mnm, msig)

let read_method_name input = 
  let clsnm = read_reftype input in
  let mnm   = read_word input in
  let msig  = read_methodsig input in
    (clsnm, mnm, msig)

let rec read_class_flags flags input = match input#tok with
  | WORD "public"     -> input#advance (); read_class_flags {flags with AF.c_public=true} input
  | WORD "private"    -> input#advance (); read_class_flags {flags with AF.c_private=true} input
  | WORD "protected"  -> input#advance (); read_class_flags {flags with AF.c_protected=true} input
  | WORD "static"     -> input#advance (); read_class_flags {flags with AF.c_static=true} input
  | WORD "final"      -> input#advance (); read_class_flags {flags with AF.c_final=true} input
  | WORD "super"      -> input#advance (); read_class_flags {flags with AF.c_super=true} input (* FIXME: have super by default? and a 'notsuper' flag? *)
  | WORD "abstract"   -> input#advance (); read_class_flags {flags with AF.c_abstract=true} input
  | WORD "synthetic"  -> input#advance (); read_class_flags {flags with AF.c_synthetic=true} input
  | WORD "annotation" -> input#advance (); read_class_flags {flags with AF.c_annotation=true} input
  | WORD "enum"       -> input#advance (); read_class_flags {flags with AF.c_enum=true} input
  | _                 -> flags

let rec read_method_flags flags input = match input#tok with
  | WORD "public"       -> input#advance (); read_method_flags {flags with AF.m_public=true} input
  | WORD "private"      -> input#advance (); read_method_flags {flags with AF.m_private=true} input
  | WORD "protected"    -> input#advance (); read_method_flags {flags with AF.m_protected=true} input
  | WORD "static"       -> input#advance (); read_method_flags {flags with AF.m_static=true} input
  | WORD "final"        -> input#advance (); read_method_flags {flags with AF.m_final=true} input
  | WORD "synchronized" -> input#advance (); read_method_flags {flags with AF.m_synchronized=true} input
  | WORD "bridge"       -> input#advance (); read_method_flags {flags with AF.m_bridge=true} input
  | WORD "varargs"      -> input#advance (); read_method_flags {flags with AF.m_varargs=true} input
  | WORD "native"       -> input#advance (); read_method_flags {flags with AF.m_native=true} input
  | WORD "abstract"     -> input#advance (); read_method_flags {flags with AF.m_abstract=true} input
  | WORD "strictfp"     -> input#advance (); read_method_flags {flags with AF.m_strictfp=true} input
  | WORD "synthetic"    -> input#advance (); read_method_flags {flags with AF.m_synthetic=true} input
  | _                   -> flags

let rec read_field_flags flags input = match input#tok with
  | WORD "public"     -> input#advance (); read_field_flags {flags with AF.f_public=true} input
  | WORD "private"    -> input#advance (); read_field_flags {flags with AF.f_private=true} input
  | WORD "protected"  -> input#advance (); read_field_flags {flags with AF.f_protected=true} input
  | WORD "static"     -> input#advance (); read_field_flags {flags with AF.f_static=true} input
  | WORD "final"      -> input#advance (); read_field_flags {flags with AF.f_final=true} input
  | WORD "volatile"   -> input#advance (); read_field_flags {flags with AF.f_volatile=true} input
  | WORD "transient"  -> input#advance (); read_field_flags {flags with AF.f_transient=true} input
  | WORD "synthetic"  -> input#advance (); read_field_flags {flags with AF.f_synthetic=true} input
  | WORD "enum"       -> input#advance (); read_field_flags {flags with AF.f_enum=true} input
  | _                 -> flags

let rec read_annotation input =
  let typ = read_jtype input in
  let _   = read_newline input in
  let els = read_elements [] input in
  let _   = read_directive "end" input in
  let _   = read_specific_word "annotation" input in
  let _   = read_newline input in
    (typ, els)

and read_element ~allow_end input () = match input#tok with
  | DIRECTIVE "byte" ->
      let _ = input#advance () in
      let b = read_int input in
      let _ = read_newline input in
	Some (CD.Const_byte b)
  | DIRECTIVE "char" ->
      let _ = input#advance () in
      let c = read_int32 input in
      let _ = read_newline input in
	Some (CD.Const_char c)
  | DIRECTIVE "double" ->
      let _ = input#advance () in
      let d = read_double input in
      let _ = read_newline input in
	Some (CD.Const_double d)
  | DIRECTIVE "float" -> 
      let _ = input#advance () in
      let f = read_double input in
      let _ = read_newline input in
	Some (CD.Const_float (JFloat.of_float f))
  | DIRECTIVE "int" ->
      let _ = input#advance () in
      let i = read_int32 input in
      let _ = read_newline input in
	Some (CD.Const_int i)
  | DIRECTIVE "long" ->
      let _ = input#advance () in
      let l = read_int64 input in
      let _ = read_newline input in
	Some (CD.Const_long l)
  | DIRECTIVE "short" ->
      let _ = input#advance () in
      let s = read_int input in
      let _ = read_newline input in
	Some (CD.Const_short s)
  | DIRECTIVE "boolean" ->
      let _ = input#advance () in
      let b = read_int input in
      let _ = read_newline input in
	Some (CD.Const_bool b)
  | DIRECTIVE "string" ->
      let _ = input#advance () in
      let s = read_string input in
      let _ = read_newline input in
	Some (CD.Const_string s)
  | DIRECTIVE "annotation" ->
      let _ = input#advance () in
      let a = read_annotation input in
	Some (CD.Annot_Value a)
  | DIRECTIVE "enumval" ->
      let _     = input#advance () in
      let clsnm = read_classname input in
      let v     = read_word input in
      let _     = read_newline input in
	Some (CD.Enum_Const_Value (clsnm, v))
  | DIRECTIVE "class" ->
      let _  = input#advance () in
      let ci = read_word input in (* FIXME: is this correct? *)
      let _  = read_newline input in
	Some (CD.Class_Info ci)
  | DIRECTIVE "array" ->
      let _   = input#advance () in
      let _   = read_newline input in
      let els = Util.repeat_until_None (read_element ~allow_end:true input) in
      let _   = read_directive "end" input in
      let _   = read_specific_word "array" input in
	Some (CD.Array_Value els)
  | DIRECTIVE "end" when allow_end ->
      None
  | DIRECTIVE d ->
      raise (Parse_error ("unknown annotation element type: " ^ d, input#pos))
  | STRINGLIT _
  | WORD _
  | NEWLINE
  | EOF ->
      raise (Parse_error ("expecting annotation element type directive", input#pos))

and read_elements els input = match input#tok with
  | NEWLINE ->
      input#advance ();
      read_elements els input
  | DIRECTIVE "element" ->
      let _    = input#advance () in
      let name = read_word input in
      let el   = Option.get (read_element ~allow_end:false input ()) in
	read_elements ((name,el)::els) input
  | DIRECTIVE "end" ->
      List.rev els
  | DIRECTIVE d ->
      raise (Parse_error ("unexpected directive in annotation: " ^ d, input#pos))
  | STRINGLIT _
  | WORD _
  | EOF ->
      raise (Parse_error ("expecting '.element' or '.end' inside annotation", input#pos))

let (+?+) x xs = match xs with None -> Some [x] | Some xs -> Some (x::xs)

let read_code input parsers =
  let new_label, new_label_defn, new_label_use =
    let label_gen = Label.label_generator () in
    let defn_set  = Hashtbl.create 10 in
    let use_set   = Hashtbl.create 10 in

    let new_label () = Label.new_label label_gen in
    let new_label_use nm pos =
      try fst (Hashtbl.find use_set nm) with
	| Not_found ->
	    let l = new_label () in
	    let _ = Hashtbl.add use_set nm (l,pos) in
	      l in
    let new_label_defn nm pos =
      if Hashtbl.mem defn_set nm then
	raise (Parse_error ("repeated label: '" ^ nm ^ "'", pos))
      else 
	(Hashtbl.add defn_set nm ();
	 new_label_use nm pos)
    in
      new_label, new_label_defn, new_label_use
  in
  let read_label input = 
    let pos = input#pos in
    let l   = read_word input in
      new_label_use l pos
  in
  let read_instr_param loop reader instr code =
    let _ = input#advance () in
    let n = reader input in
    let _ = read_newline input in
      loop {code with CD.code_code=instr n::code.CD.code_code}
  in
    (* FIXME: TODO: local variable information, stack maps. Want to integrate them with the instruction stream? *)
  let rec read_code_internal code = match input#tok with
    | NEWLINE ->
	input#advance ();
	read_code_internal code
    | DIRECTIVE "end" ->
	input#advance ();
	read_specific_word "code" input;
	read_newline input;
	{code with
	     CD.code_code             = List.rev code.CD.code_code
	   ; CD.code_handlers         = List.rev code.CD.code_handlers
	   ; CD.code_line_numbers     = Option.map List.rev code.CD.code_line_numbers
	   ; CD.code_localvars        = Option.map List.rev code.CD.code_localvars
	   ; CD.code_localvartypes    = Option.map List.rev code.CD.code_localvartypes
	   ; CD.code_stackmap         = Option.map List.rev code.CD.code_stackmap
	   ; CD.code_cldc_stackmap    = Option.map List.rev code.CD.code_cldc_stackmap
	   ; CD.code_generic_attributes = List.rev code.CD.code_generic_attributes
	}
    | DIRECTIVE "max_stack" ->
	input#advance ();
	let n = read_int input in
	let code = {code with CD.code_max_stack=n} in
	  read_code_internal code
    | DIRECTIVE "locals" ->
	input#advance ();
	let n = read_int input in
	let code = {code with CD.code_locals=n} in
	  read_code_internal code
    | DIRECTIVE "line" ->
	let _    = input#advance () in
	let n    = read_int input in
	let l    = new_label () in
	let code = {code with
		        CD.code_code=BC.Jlabel (l, ())::code.CD.code_code
		      ; CD.code_line_numbers={CD.ln_start=l; CD.ln_line=n} +?+ code.CD.code_line_numbers} in
	  read_code_internal code
    | DIRECTIVE "catch" ->
	let _ = input#advance () in
	let ty = (match input#tok with
		    | WORD "any" -> input#advance (); None
		    | WORD s -> (match JT.class_of_string s with
				   | Some ty -> input#advance (); Some ty
				   | None    -> raise (Parse_error ("expecting 'any' or a class name", input#pos)))
		    | _ ->
			raise (Parse_error ("expecting 'any' or a class name", input#pos))) in
	let _         = read_specific_word "from" input in
	let exn_start = read_label input in
	let _         = read_specific_word "to" input in
	let exn_end   = read_label input in
	let _         = read_specific_word "using" input in
	let exn_entry = read_label input in
	let _         = read_newline input in
	let hdl       = { CD.exn_catch = ty
			; CD.exn_start = exn_start
			; CD.exn_end   = exn_end
			; CD.exn_entry = exn_entry
			} in
	  read_code_internal {code with CD.code_handlers=hdl::code.CD.code_handlers}
    | DIRECTIVE "attribute" ->
	input#advance ();
	let name  = read_string input in
	let value = read_string input in
	let _     = read_newline input in
	let code  = {code with CD.code_generic_attributes=(name,value)::code.CD.code_generic_attributes} in
	  read_code_internal code
    | DIRECTIVE d            ->
	(match try Some (Hashtbl.find parsers.parser_custom_attr_code d) with Not_found -> None with
	   | None ->
	       raise (Parse_error ("unknown directive in code: " ^ d, input#pos))
	   | Some attr_parser ->
	       let _ = input#advance () in
	       let a = attr_parser input new_label_use code.CD.code_custom_attributes in
	       let _ = read_newline input in
		 read_code_internal {code with CD.code_custom_attributes = a})
    | WORD s when s.[String.length s - 1] = ':' ->
	if String.length s = 1 then
	  raise (Parse_error ("invalid label", input#pos));
	let label_str = String.sub s 0 (String.length s - 1) in
	let l         = new_label_defn label_str input#pos in
	let _         = input#advance () in
	  read_code_internal {code with CD.code_code=BC.Jlabel (l,())::code.CD.code_code}
    | WORD "aaload"      -> read_instr BC.Jaaload code
    | WORD "aastore"     -> read_instr BC.Jaastore code
    | WORD "aconst_null" -> read_instr BC.Jaconst_null code
    | WORD "aload"       -> read_instr_int (fun i -> BC.Jaload i) code
    | WORD "arraylength" -> read_instr BC.Jarraylength code
    | WORD "astore"      -> read_instr_int (fun i -> BC.Jastore i) code
    | WORD "athrow"      -> read_instr BC.Jathrow code
    | WORD "baload"      -> read_instr BC.Jbaload code
    | WORD "bastore"     -> read_instr BC.Jbastore code
    | WORD "caload"      -> read_instr BC.Jcaload code
    | WORD "castore"     -> read_instr BC.Jcastore code
    | WORD "checkcast"   -> read_instr_reftype (fun ty -> BC.Jcheckcast ty) code
    | WORD "classconst"  -> read_instr_reftype (fun ty -> BC.Jclassconst ty) code
    | WORD "d2f"         -> read_instr BC.Jd2f code
    | WORD "d2i"         -> read_instr BC.Jd2i code
    | WORD "d2l"         -> read_instr BC.Jd2l code
    | WORD "dadd"        -> read_instr BC.Jdadd code
    | WORD "daload"      -> read_instr BC.Jdaload code
    | WORD "dastore"     -> read_instr BC.Jdastore code
    | WORD "dcmpg"       -> read_instr BC.Jdcmpg code
    | WORD "dcmpl"       -> read_instr BC.Jdcmpl code
    | WORD "dconst"      -> read_instr_double (fun d -> BC.Jdconst d) code
    | WORD "ddiv"        -> read_instr BC.Jddiv code
    | WORD "dload"       -> read_instr_int (fun i -> BC.Jdload i) code
    | WORD "dmul"        -> read_instr BC.Jdmul code
    | WORD "dneg"        -> read_instr BC.Jdneg code
    | WORD "drem"        -> read_instr BC.Jdrem code
    | WORD "dstore"      -> read_instr_int (fun i -> BC.Jdstore i) code
    | WORD "dsub"        -> read_instr BC.Jdsub code
    | WORD "dup"         -> read_instr BC.Jdup code
    | WORD "dup_x1"      -> read_instr BC.Jdup_x1 code
    | WORD "dup_x2"      -> read_instr BC.Jdup_x2 code
    | WORD "dup2"        -> read_instr BC.Jdup2 code
    | WORD "dup2_x1"     -> read_instr BC.Jdup2_x1 code
    | WORD "dup2_x2"     -> read_instr BC.Jdup2_x2 code
    | WORD "f2d"         -> read_instr BC.Jf2d code
    | WORD "f2i"         -> read_instr BC.Jf2i code
    | WORD "f2l"         -> read_instr BC.Jf2l code
    | WORD "fadd"        -> read_instr BC.Jfadd code
    | WORD "faload"      -> read_instr BC.Jfaload code
    | WORD "fastore"     -> read_instr BC.Jfastore code
    | WORD "fcmpg"       -> read_instr BC.Jfcmpg code
    | WORD "fcmpl"       -> read_instr BC.Jfcmpl code
    | WORD "fconst"      -> read_instr_float (fun f -> BC.Jfconst f) code
    | WORD "fdiv"        -> read_instr BC.Jfdiv code
    | WORD "fload"       -> read_instr_int (fun i -> BC.Jfload i) code
    | WORD "fmul"        -> read_instr BC.Jfmul code
    | WORD "fneg"        -> read_instr BC.Jfneg code
    | WORD "frem"        -> read_instr BC.Jfrem code
    | WORD "fstore"      -> read_instr_int (fun i -> BC.Jfstore i) code
    | WORD "fsub"        -> read_instr BC.Jfsub code
    | WORD "getfield"    -> read_instr_field (fun (clsnm, nm, ty) -> BC.Jgetfield (clsnm, nm, ty)) code
    | WORD "getstatic"   -> read_instr_field (fun (clsnm, nm, ty) -> BC.Jgetstatic (clsnm, nm, ty)) code
    | WORD "goto"        -> read_instr_label (fun l -> BC.Jgoto l) code
    | WORD "i2b"         -> read_instr BC.Ji2b code
    | WORD "i2c"         -> read_instr BC.Ji2c code
    | WORD "i2d"         -> read_instr BC.Ji2d code
    | WORD "i2f"         -> read_instr BC.Ji2f code
    | WORD "i2l"         -> read_instr BC.Ji2l code
    | WORD "i2s"         -> read_instr BC.Ji2s code
    | WORD "iadd"        -> read_instr BC.Jiadd code
    | WORD "iaload"      -> read_instr BC.Jiaload code
    | WORD "iand"        -> read_instr BC.Jiand code
    | WORD "iastore"     -> read_instr BC.Jiastore code
    | WORD "iconst"      -> read_instr_int32 (fun i -> BC.Jiconst i) code
    | WORD "idiv"        -> read_instr BC.Jidiv code
    | WORD "if_acmpeq"   -> read_instr_label (fun l -> BC.Jif_acmpeq l) code
    | WORD "if_acmpne"   -> read_instr_label (fun l -> BC.Jif_acmpne l) code
    | WORD "if_icmpeq"   -> read_instr_label (fun l -> BC.Jif_icmpeq l) code
    | WORD "if_icmpne"   -> read_instr_label (fun l -> BC.Jif_icmpne l) code
    | WORD "if_icmplt"   -> read_instr_label (fun l -> BC.Jif_icmplt l) code
    | WORD "if_icmpge"   -> read_instr_label (fun l -> BC.Jif_icmpge l) code
    | WORD "if_icmpgt"   -> read_instr_label (fun l -> BC.Jif_icmpgt l) code
    | WORD "if_icmple"   -> read_instr_label (fun l -> BC.Jif_icmple l) code
    | WORD "ifeq"        -> read_instr_label (fun l -> BC.Jifeq l) code
    | WORD "ifne"        -> read_instr_label (fun l -> BC.Jifne l) code
    | WORD "iflt"        -> read_instr_label (fun l -> BC.Jiflt l) code
    | WORD "ifge"        -> read_instr_label (fun l -> BC.Jifge l) code
    | WORD "ifgt"        -> read_instr_label (fun l -> BC.Jifgt l) code
    | WORD "ifle"        -> read_instr_label (fun l -> BC.Jifle l) code
    | WORD "ifnonnull"   -> read_instr_label (fun l -> BC.Jifnonnull l) code
    | WORD "ifnull"      -> read_instr_label (fun l -> BC.Jifnull l) code
    | WORD "iinc"        -> read_instr_int_int (fun (m, n) -> BC.Jiinc (m,n)) code
    | WORD "iload"       -> read_instr_int (fun i -> BC.Jiload i) code
    | WORD "imul"        -> read_instr BC.Jimul code
    | WORD "ineg"        -> read_instr BC.Jineg code
    | WORD "instanceof"  -> read_instr_reftype (fun ty -> BC.Jinstanceof ty) code
    | WORD "invokeinterface" -> read_instr_imethod (fun (clsnm, nm, msig) -> BC.Jinvokeinterface (clsnm, nm, msig)) code
    | WORD "invokespecial"   -> read_instr_method (fun (clsnm, nm, msig) -> BC.Jinvokespecial (clsnm, nm, msig)) code
    | WORD "invokestatic"    -> read_instr_method (fun (clsnm, nm, msig) -> BC.Jinvokestatic (clsnm, nm, msig)) code
    | WORD "invokevirtual"   -> read_instr_method (fun (clsnm, nm, msig) -> BC.Jinvokevirtual (clsnm, nm, msig)) code
    | WORD "ior"         -> read_instr BC.Jior code
    | WORD "irem"        -> read_instr BC.Jirem code
    | WORD "ishl"        -> read_instr BC.Jishl code
    | WORD "ishr"        -> read_instr BC.Jishr code
    | WORD "istore"      -> read_instr_int (fun i -> BC.Jistore i) code
    | WORD "isub"        -> read_instr BC.Jisub code
    | WORD "iushr"       -> read_instr BC.Jiushr code
    | WORD "ixor"        -> read_instr BC.Jixor code
    | WORD "jsr"         -> read_instr_label (fun l -> BC.Jjsr l) code
    | WORD "l2d"         -> read_instr BC.Jl2d code
    | WORD "l2f"         -> read_instr BC.Jl2f code
    | WORD "l2i"         -> read_instr BC.Jl2i code
    | WORD "ladd"        -> read_instr BC.Jladd code
    | WORD "laload"      -> read_instr BC.Jlaload code
    | WORD "land"        -> read_instr BC.Jland code
    | WORD "lastore"     -> read_instr BC.Jlastore code
    | WORD "lcmp"        -> read_instr BC.Jlcmp code
    | WORD "lconst"      -> read_instr_int64 (fun i -> BC.Jlconst i) code
    | WORD "ldiv"        -> read_instr BC.Jldiv code
    | WORD "lload"       -> read_instr_int (fun i -> BC.Jlload i) code
    | WORD "lmul"        -> read_instr BC.Jlmul code
    | WORD "lneg"        -> read_instr BC.Jlneg code
    | WORD "lookupswitch"-> read_instr_lookupswitch code
    | WORD "lor"         -> read_instr BC.Jlor code
    | WORD "lrem"        -> read_instr BC.Jlrem code
    | WORD "lshl"        -> read_instr BC.Jlshl code
    | WORD "lshr"        -> read_instr BC.Jlshr code
    | WORD "lstore"      -> read_instr_int (fun i -> BC.Jlstore i) code
    | WORD "lsub"        -> read_instr BC.Jlsub code
    | WORD "lushr"       -> read_instr BC.Jlushr code
    | WORD "lxor"        -> read_instr BC.Jlxor code
    | WORD "monitorenter"-> read_instr BC.Jmonitorenter code
    | WORD "monitorexit" -> read_instr BC.Jmonitorexit code
    | WORD "new"         -> read_instr_class (fun clsnm -> BC.Jnew clsnm) code
    | WORD "newarray"    -> read_instr_newarray code
    | WORD "nop"         -> read_instr BC.Jnop code
    | WORD "pop"         -> read_instr BC.Jpop code
    | WORD "pop2"        -> read_instr BC.Jpop2 code
    | WORD "putfield"    -> read_instr_field (fun (clsnm, nm, ty) -> BC.Jputfield (clsnm, nm, ty)) code
    | WORD "putstatic"   -> read_instr_field (fun (clsnm, nm, ty) -> BC.Jputstatic (clsnm, nm, ty)) code
    | WORD "ret"         -> read_instr_int (fun i -> BC.Jret i) code
    | WORD "return"      -> read_instr BC.Jreturn code
    | WORD "saload"      -> read_instr BC.Jsaload code
    | WORD "sconst"      -> read_instr_string (fun s -> BC.Jsconst s) code
    | WORD "swap"        -> read_instr BC.Jswap code
    | WORD "tableswitch" -> read_tableswitch code
    | WORD w             -> raise (Parse_error ("unknown instruction: " ^ w, input#pos))
    | STRINGLIT _        -> raise (Parse_error ("unexpected string literal", input#pos))
    | EOF                -> raise (Parse_error ("unexpected end-of-file", input#pos))
  and read_instr instr code =
    input#advance ();
    read_newline input;
    read_code_internal {code with CD.code_code=instr::code.CD.code_code}
  and read_instr_int     i = read_instr_param read_code_internal read_int i
  and read_instr_reftype i = read_instr_param read_code_internal read_reftype i
  and read_instr_double  i = read_instr_param read_code_internal read_double i
  and read_instr_float   i = read_instr_param read_code_internal (fun input -> let n = read_double input in JFloat.of_float n) i
  and read_instr_field   i = read_instr_param read_code_internal read_field_name i
  and read_instr_label   i = read_instr_param read_code_internal read_label i
  and read_instr_int32   i = read_instr_param read_code_internal read_int32 i
  and read_instr_int_int i = read_instr_param read_code_internal (fun input -> let n1 = read_int input in let n2 = read_int input in (n1,n2)) i
  and read_instr_imethod i = read_instr_param read_code_internal read_imethod_name i
  and read_instr_method  i = read_instr_param read_code_internal read_method_name i
  and read_instr_int64   i = read_instr_param read_code_internal read_int64 i
  and read_instr_class   i = read_instr_param read_code_internal read_classname i
  and read_instr_string  i = read_instr_param read_code_internal read_string i
  and read_instr_newarray code = read_instr_param read_code_internal
    (fun input ->
       let ty = read_jtype input in
       let n  = read_int input in
	 (ty, n))
    (fun (ty, n) -> BC.Jnewarray (ty,n))
    code
  and read_tableswitch code        = assert false (* FIXME *)
  and read_instr_lookupswitch code = assert false (* FIXME *)
  in
    read_code_internal (CD.code ~max_stack:0 ~locals:0 ~code:[] ~custom_attributes:parsers.empty_code_attribute ())

let read_method meth input parsers =
  let rec read_method_internal meth = match input#tok with
    | NEWLINE                -> input#advance (); read_method_internal meth
    | DIRECTIVE "deprecated" -> input#advance (); read_deprecated meth
    | DIRECTIVE "synthetic"  -> input#advance (); read_synthetic meth
    | DIRECTIVE "signature"  -> input#advance (); read_signature meth
    | DIRECTIVE "throws"     -> input#advance (); read_throws meth
    | DIRECTIVE "end"        -> input#advance (); read_end meth
    | DIRECTIVE "code"       -> input#advance (); read_code_inside_method meth
    | DIRECTIVE "annotation" -> input#advance (); read_method_annotation meth
    | DIRECTIVE "attribute"  -> input#advance (); read_method_generic_attribute meth
    | DIRECTIVE d            ->
	(match try Some (Hashtbl.find parsers.parser_custom_attr_method d) with Not_found -> None with
	   | None ->
	       raise (Parse_error ("unknown directive in method: " ^ d, input#pos))
	   | Some attr_parser ->
	       let _ = input#advance () in
	       let a = attr_parser input meth.CD.md_custom_attributes in
	       let _ = read_newline input in
		 read_method_internal {meth with CD.md_custom_attributes = a})
    | EOF                    -> raise (Parse_error ("unexpected end-of-file inside method", input#pos))
    | STRINGLIT _            -> raise (Parse_error ("unexpected string literal inside method", input#pos))
    | WORD _                 -> raise (Parse_error ("unexpected bare word", input#pos))

  and read_method_generic_attribute meth =
    let name  = read_string input in
    let value = read_string input in
    let _     = read_newline input in
      read_method_internal {meth with CD.md_generic_attributes=(name,value)::meth.CD.md_generic_attributes}

  (* FIXME: do parameter annotations, and annotation default *)
  and read_method_annotation meth =
    let typ_pos = input#pos in
    let typ     = read_word input in
    let annot   = read_annotation input in
    let meth    =
      (match typ with
	 | "visible"        -> {meth with CD.md_visible_annotations=annot::meth.CD.md_visible_annotations}
	 | "invisible"      -> {meth with CD.md_invisible_annotations=annot::meth.CD.md_invisible_annotations}
(* FIXME | "visibleparam"   -> {meth with CD.md_visible_param_annotations=annot::meth.CD.md_visible_param_annotations}
	 | "invisibleparam" -> {meth with CD.md_invisible_param_annotations=annot::meth.CD.md_invisible_param_annotations}*)
	 | _           -> raise (Parse_error ("method annotations must be one of 'visible', 'invisible', 'visibleparam' or 'invisibleparam'", typ_pos))) in
      read_method_internal meth

  and read_code_inside_method meth =
    if meth.CD.md_code <> None then
      raise (Parse_error ("only one .code is permitted in a method", input#pos));
    let _    = read_newline input in
    let code = read_code input parsers in
      read_method_internal {meth with CD.md_code=Some code}

  and read_deprecated meth =
    read_newline input;
    read_method_internal {meth with CD.md_deprecated=true}

  and read_synthetic meth =
    read_newline input;
    read_method_internal {meth with CD.md_synthetic=true}

  and read_signature meth =
    if meth.CD.md_signature <> None then
      raise (Parse_error ("multiple signatures not permitted", input#pos));
    let s = read_string input in
    let _ = read_newline input in
      read_method_internal {meth with CD.md_signature=Some s}

  and read_throws meth =
    let ty = read_classname input in
    let _  = read_newline input in
      read_method_internal {meth with CD.md_exceptions=ty::meth.CD.md_exceptions}

  and read_end meth =
    read_specific_word "method" input;
    read_newline input;
    {meth with
         CD.md_exceptions                  = List.rev meth.CD.md_exceptions
       ; CD.md_generic_attributes            = List.rev meth.CD.md_generic_attributes
       ; CD.md_visible_annotations         = List.rev meth.CD.md_visible_annotations
       ; CD.md_invisible_annotations       = List.rev meth.CD.md_invisible_annotations
       ; CD.md_visible_param_annotations   = List.rev meth.CD.md_visible_param_annotations
       ; CD.md_invisible_param_annotations = List.rev meth.CD.md_invisible_param_annotations
    }
  in
    read_method_internal meth

let read_field field parsers input =
  let rec read_field_internal field = match input#tok with
    | NEWLINE -> input#advance (); read_field_internal field
    | DIRECTIVE "constantvalue" -> input#advance (); read_field_constant field
    | DIRECTIVE "annotation"    -> input#advance (); read_field_annotation field
    | DIRECTIVE "deprecated"    -> input#advance (); read_deprecated field
    | DIRECTIVE "synthetic"     -> input#advance (); read_synthetic field
    | DIRECTIVE "signature"     -> input#advance (); read_signature field
    | DIRECTIVE "attribute"     -> input#advance (); read_attribute field
    | DIRECTIVE "end"           -> input#advance (); read_end field
    | DIRECTIVE d            ->
	(match try Some (Hashtbl.find parsers.parser_custom_attr_field d) with Not_found -> None with
	   | None ->
	       raise (Parse_error ("unknown directive in method: " ^ d, input#pos))
	   | Some attr_parser ->
	       let _ = input#advance () in
	       let a = attr_parser input field.CD.fd_custom_attributes in
	       let _ = read_newline input in
		 read_field_internal {field with CD.fd_custom_attributes = a})
    | EOF                       -> raise (Parse_error ("unexpected end-of-file inside field", input#pos))
    | STRINGLIT _               -> raise (Parse_error ("unexpected string literal inside field", input#pos))
    | WORD _                    -> raise (Parse_error ("unexpected bare word inside field", input#pos))

  and read_field_constant field =
    let con = (match field.CD.fd_ty with
		 | JT.TBoolean | JT.TInt | JT.TShort | JT.TChar | JT.TByte ->
		     CD.Cint (read_int32 input)
		 | JT.TFloat ->
		     CD.Cfloat (let d = read_double input in JFloat.of_float d)
		 | JT.TDouble ->
		     CD.Cdouble (read_double input)
		 | JT.TLong ->
		     CD.Clong (read_int64 input)
		 | JT.TRef (JT.TObject (["java";"lang"], "String")) ->
		     CD.Cstring (read_string input)
		 | JT.TRef _ ->
		     raise (Parse_error ("constant value not permitted for fields of reference type other than java/lang/String", input#pos))) in
      read_newline input;
      read_field_internal {field with CD.fd_constant_value=Some con}

  and read_field_annotation field =
    let typ_pos = input#pos in
    let typ     = read_word input in
    let annot   = read_annotation input in
    let field   =
      (match typ with
	 | "visible"   -> {field with CD.fd_visible_annotations   = annot::field.CD.fd_visible_annotations }
	 | "invisible" -> {field with CD.fd_invisible_annotations = annot::field.CD.fd_invisible_annotations }
	 | _           -> raise (Parse_error ("field annotations must be either 'visible' or 'invisible'", typ_pos))) in
      read_field_internal field

  and read_deprecated field =
    read_newline input;
    read_field_internal {field with CD.fd_deprecated = true}

  and read_synthetic field =
    read_newline input;
    read_field_internal {field with CD.fd_synthetic = true}

  and read_signature field =
    if field.CD.fd_signature <> None then
      raise (Parse_error ("multiple signatures not permitted", input#pos));
    let s = read_string input in
    let _ = read_newline input in
      read_field_internal {field with CD.fd_signature=Some s}

  and read_attribute field =
    let name  = read_string input in
    let value = read_string input in
    let _     = read_newline input in
      read_field_internal {field with CD.fd_generic_attributes=(name,value)::field.CD.fd_generic_attributes}

  and read_end field =
    read_specific_word "field" input;
    read_newline input;
    {field with
         CD.fd_generic_attributes      = List.rev field.CD.fd_generic_attributes
       ; CD.fd_visible_annotations   = List.rev field.CD.fd_visible_annotations
       ; CD.fd_invisible_annotations = List.rev field.CD.fd_invisible_annotations
    }
  in
    read_field_internal field

let rec read input parsers = 
  let rec read_class_inner cd = match input#tok with
    | NEWLINE                -> input#advance (); read_class_inner cd
    | DIRECTIVE "bytecode"   -> input#advance (); read_major_minor cd
    | DIRECTIVE "source"     -> input#advance (); read_source cd
    | DIRECTIVE "interface"  -> input#advance (); read_interface_decl cd
    | DIRECTIVE "class"      -> input#advance (); read_class_decl cd
    | DIRECTIVE "super"      -> input#advance (); read_super_decl cd
    | DIRECTIVE "implements" -> input#advance (); read_implements cd
    | DIRECTIVE "field"      -> input#advance (); read_field_inside_class cd
    | DIRECTIVE "method"     -> input#advance (); read_method_inside_class cd
    | DIRECTIVE "deprecated" -> input#advance (); read_deprecated cd
    | DIRECTIVE "synthetic"  -> input#advance (); read_synthetic cd
    | DIRECTIVE "enclosing"  -> input#advance (); read_enclosing_method cd
    | DIRECTIVE "debug"      -> input#advance (); read_debug cd
    | DIRECTIVE "signature"  -> input#advance (); read_signature cd
    | DIRECTIVE "annotation" -> input#advance (); read_class_annotation cd
    | DIRECTIVE "attribute"  -> input#advance (); read_class_generic_attribute cd
    | DIRECTIVE d            ->
	(match try Some (Hashtbl.find parsers.parser_custom_attr_class d) with Not_found -> None with
	   | None ->
	       raise (Parse_error ("unknown directive in code: " ^ d, input#pos))
	   | Some attr_parser ->
	       let (named_flag,cd) = cd in
	       let _               = input#advance () in
	       let a               = attr_parser input cd.CD.custom_attributes in
	       let _               = read_newline input in
		 read_class_inner (named_flag, {cd with CD.custom_attributes = a}))
    | EOF                    -> cd
    | STRINGLIT _            -> raise (Parse_error ("unexpected string literal", input#pos))
    | WORD _                 -> raise (Parse_error ("unexpected bare word", input#pos))

  and read_major_minor (named_flag,cd) =
    match input#tok with
      | WORD s ->
	  let cd =
	    try
	      Scanf.sscanf s "%u.%u%!" (fun major minor -> {cd with CD.major = major; CD.minor = minor})
	    with
	      | Failure _
	      | Scanf.Scan_failure _
	      | End_of_file ->
		  raise (Parse_error ("bad major.minor version numbers", input#pos)) in
	  let _ = input#advance () in
	  let _ = read_newline input in
	    read_class_inner (named_flag,cd)
      | t ->
	  raise (Parse_error ("bad major.minor version numbers", input#pos))

  and read_source (named_flag,cd) =
    if cd.CD.srcfile <> None then
      raise (Parse_error ("Only one .source directive is permitted", input#pos));
    let s  = read_string input in
    let cd = {cd with CD.srcfile = Some s} in
    let _  = read_newline input in
      read_class_inner (named_flag,cd)

  and read_class_or_interface_decl base_flags (named_flag,cd) =
    if named_flag then
      raise (Parse_error ("Only one of .class or .interface permitted", input#pos));
    let flags = read_class_flags base_flags input in
    let clsnm = read_classname input in
    let _     = read_newline input in
      read_class_inner (true, {cd with CD.this=clsnm; CD.flags=flags})

  and read_class_decl cd =
    read_class_or_interface_decl AF.empty_class_flags cd
  and read_interface_decl cd =
    read_class_or_interface_decl {AF.empty_class_flags with AF.c_interface=true} cd
      
  and read_super_decl (named_flag,cd) =
    if cd.CD.super <> None then
      raise (Parse_error ("Only one .super directive is permitted", input#pos));
    let clsnm = read_classname input in
    let cd    = {cd with CD.super=Some clsnm} in
    let _     = read_newline input in
      read_class_inner (named_flag,cd)

  and read_implements (named_flag,cd) =
    let clsnm = read_classname input in
    let _     = read_newline input in
    let cd    = {cd with CD.interfaces=clsnm::cd.CD.interfaces} in
      read_class_inner (named_flag,cd)

  and read_field_inside_class (named_flag,cd) =
    let flags = read_field_flags AF.empty_field_flags input in
    let fnm   = read_word input in
    let fty   = read_jtype input in
    let _     = read_newline input in
    let field = read_field (CD.field_decl ~flags:flags ~name:fnm ~ty:fty ~custom_attributes:parsers.empty_field_attribute ()) parsers input in
    let cd    = {cd with CD.fields=field::cd.CD.fields} in
      read_class_inner (named_flag,cd)

  and read_method_inside_class (named_flag,cd) =
    let flags = read_method_flags AF.empty_method_flags input in
    let mnm   = read_word input in
    let msig  = read_methodsig input in
    let _     = read_newline input in
    let meth  = read_method (CD.method_decl ~flags:flags ~name:mnm ~msig:msig ~custom_attributes:parsers.empty_method_attribute ()) input parsers in
    let cd    = {cd with CD.methods=meth::cd.CD.methods} in
      read_class_inner (named_flag,cd)

  and read_deprecated (named_flag,cd) =
    read_newline input;
    read_class_inner (named_flag, {cd with CD.deprecated=true})

  and read_synthetic (named_flag,cd) =
    read_newline input;
    read_class_inner (named_flag, {cd with CD.synthetic=true})
      
  and read_class_annotation (named_flag,cd) =
    let typ_pos = input#pos in
    let typ     = read_word input in
    let annot   = read_annotation input in
    let cd      =
      (match typ with
	 | "visible"   -> {cd with CD.visible_annotations=annot::cd.CD.visible_annotations}
	 | "invisible" -> {cd with CD.invisible_annotations=annot::cd.CD.invisible_annotations}
	 | _           -> raise (Parse_error ("Class annotations must be 'visible' or 'invisible'", typ_pos))) in
      read_class_inner (named_flag, cd)

  and read_enclosing_method (named_flag,cd) =
    if cd.CD.enclosing_method <> None then
      raise (Parse_error ("Only one enclosing method declaration permitted", input#pos));
    let _     = read_specific_word "method" input in
    let clsnm = read_classname input in
    let meth  = (if input#tok = NEWLINE then
		   (read_newline input;
		    None)
		 else
		   (let name = read_word input in
		    let msig = read_methodsig input in
		      read_newline input;
		      Some (name, msig))) in
    let enc_method = { CD.ec_class = clsnm; CD.ec_method = meth } in
    let cd         = { cd with CD.enclosing_method = Some enc_method } in
      read_class_inner (named_flag, cd)

  and read_debug (named_flag, cd) =
    if cd.CD.source_debug_extn <> None then
      raise (Parse_error ("Only one .debug declaration permitted", input#pos));
    let s  = read_string input in
    let _  = read_newline input in
    let cd = {cd with CD.source_debug_extn=Some s} in
      read_class_inner (named_flag,cd)
	
  and read_signature (named_flag,cd) =
    if cd.CD.signature <> None then
      raise (Parse_error ("Only one .signature declaration permitted", input#pos));
    let s  = read_string input in
    let _  = read_newline input in
    let cd = {cd with CD.signature=Some s} in
      read_class_inner (named_flag,cd)

  and read_class_generic_attribute (named_flag,cd) =
    let name  = read_string input in
    let value = read_string input in
    let _     = read_newline input in
      read_class_inner (named_flag, {cd with CD.generic_attributes=(name,value)::cd.CD.generic_attributes})
  in
  let cd            = CD.class_decl ~flags:AF.empty_class_flags ~this:([],"") ~super:None ~fields:[] ~methods:[] ~custom_attributes:parsers.empty_class_attribute () in
  let named_flag,cd = read_class_inner (false,cd) in
    if not named_flag then
      raise (Parse_error ("No class name provided", input#pos));
    {cd with
       CD.methods               = List.rev cd.CD.methods
       ; CD.fields                = List.rev cd.CD.fields
       ; CD.interfaces            = List.rev cd.CD.interfaces
       ; CD.generic_attributes      = List.rev cd.CD.generic_attributes
       ; CD.visible_annotations   = List.rev cd.CD.visible_annotations
       ; CD.invisible_annotations = List.rev cd.CD.invisible_annotations
       ; CD.inner_classes         = List.rev cd.CD.inner_classes
    }

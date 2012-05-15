open ExtList
open Ocaml_jvml
module CD = Classdecl
module JT = Jvmtype
module AF = AccessFlags
module BC = Bytecode

let escape_string str =
  let buffer = Buffer.create (String.length str + 4) in
  let rec loop idx =
    if idx = String.length str then ()
    else begin
      (match str.[idx] with
	 | '"' -> Buffer.add_string buffer "\\\""
	 | '\\' -> Buffer.add_string buffer "\\\\"
	 | c   -> Buffer.add_char buffer c);
      loop (idx+1)
    end
  in
    loop 0;
    Buffer.contents buffer

type 'a output =
    { mutable output_indent       : int
    ;         output_output       : 'a IO.output
    ; mutable output_done_newline : bool
    }

let make_output out =
  { output_indent = 0
  ; output_output = out
  ; output_done_newline = true
  }

type token =
    [ `WORD of string
    | `STRINGLIT of string
    | `DIRECTIVE of string
    | `INT of int
    | `DOUBLE of float
    | `INT32 of int32
    | `INT64 of int64
    ]

type ('f, 'm, 'c, 'cl) custom_attr_formatters =
    { format_field_attribute  : 'f -> (string * token list) list
    ; format_method_attribute : 'm -> (string * token list) list
    ; format_code_attribute   : (Label.label -> string) -> 'c -> (string * token list) list
    ; format_class_attribute  : 'cl -> (string * token list) list
    }

let null_formatters = 
  { format_field_attribute  = (fun _ -> [])
  ; format_method_attribute = (fun _ -> [])
  ; format_code_attribute   = (fun _ _ -> [])
  ; format_class_attribute  = (fun _ -> [])
  }

let emit ?(undent=0) output tok = match tok with
  | `NEWLINE ->
      IO.write output.output_output '\n';
      output.output_done_newline <- true
  | #token as tok ->
      if output.output_done_newline then
	IO.nwrite output.output_output (String.make (output.output_indent - undent) ' ')
      else
	IO.write output.output_output ' ';
      output.output_done_newline <- false;
      (match tok with
	 | `WORD s ->
	     IO.nwrite output.output_output s
	 | `STRINGLIT s ->
	     IO.write output.output_output '"';
	     IO.nwrite output.output_output (escape_string s);
	     IO.write output.output_output '"'
	 | `DIRECTIVE s ->
	     IO.write output.output_output '.';
	     IO.nwrite output.output_output s
	 | `INT i ->
	     IO.nwrite output.output_output (Printf.sprintf "%d" i)
	 | `DOUBLE i ->
	     IO.nwrite output.output_output (Printf.sprintf "%f" i)
	 | `INT32 i ->
	     IO.nwrite output.output_output (Printf.sprintf "%ld" i)
	 | `INT64 i ->
	     IO.nwrite output.output_output (Printf.sprintf "%Ld" i))

let emit_ln output tok =
  emit output tok;
  emit output `NEWLINE

let indent output =
  output.output_indent <- output.output_indent + 2

let undent output =
  output.output_indent <- output.output_indent - 2

let emit_all output =
  List.iter (emit output)

let emit_all_ln output l =
  emit_all output l;
  emit output `NEWLINE

let emit_generic_attribute output (name,value) =
  emit_all_ln output
    [ `DIRECTIVE "attribute"
    ; `STRINGLIT name
    ; `STRINGLIT value
    ]

let emit_custom_attribute output format attr =
  List.iter (fun (directive, tokens) -> emit output (`DIRECTIVE directive); emit_all_ln output tokens) (format attr)

let emit_field_flags output flags =
  let (+>) b tok = if b then emit output (`WORD tok) in
    flags.AF.f_public    +> "public";
    flags.AF.f_private   +> "private";
    flags.AF.f_protected +> "protected";
    flags.AF.f_static    +> "static";
    flags.AF.f_final     +> "final";
    flags.AF.f_volatile  +> "volatile";
    flags.AF.f_transient +> "transient";
    flags.AF.f_synthetic +> "synthetic";
    flags.AF.f_enum      +> "enum"

let emit_constant_value output const_value = match const_value with
  | CD.Cint i    -> emit output (`WORD (Printf.sprintf "%ld" i))
  | CD.Cfloat f  -> emit output (`WORD (Printf.sprintf "%f" (JFloat.to_float f))) (* FIXME: should emit a warning here *)
  | CD.Clong l   -> emit output (`WORD (Printf.sprintf "%Ld" l))
  | CD.Cdouble d -> emit output (`WORD (Printf.sprintf "%f" d))
  | CD.Cstring s -> emit output (`STRINGLIT s)

let rec emit_annotation_element output value = match value with
  | CD.Const_byte b   -> emit_all_ln output [`DIRECTIVE "byte";    `WORD (Printf.sprintf "%d" b)]
  | CD.Const_char c   -> emit_all_ln output [`DIRECTIVE "char";    `WORD (Printf.sprintf "%ld" c)]
  | CD.Const_double d -> emit_all_ln output [`DIRECTIVE "double";  `WORD (Printf.sprintf "%f" d)]
  | CD.Const_float f  -> emit_all_ln output [`DIRECTIVE "float";   `WORD (Printf.sprintf "%f" (JFloat.to_float f))] (* FIXME: emit a warning *)
  | CD.Const_int i    -> emit_all_ln output [`DIRECTIVE "int";     `WORD (Printf.sprintf "%ld" i)]
  | CD.Const_long l   -> emit_all_ln output [`DIRECTIVE "long";    `WORD (Printf.sprintf "%Ld" l)]
  | CD.Const_short s  -> emit_all_ln output [`DIRECTIVE "short";   `WORD (Printf.sprintf "%d" s)]
  | CD.Const_bool b   -> emit_all_ln output [`DIRECTIVE "boolean"; `WORD (Printf.sprintf "%d" b)]
  | CD.Const_string s -> emit_all_ln output [`DIRECTIVE "string";  `STRINGLIT s]
  | CD.Enum_Const_Value (typ,name) -> emit_all_ln output [`DIRECTIVE "enumval"; `WORD (Jvmtype.string_of_class typ); `WORD name]
  | CD.Class_Info ci  -> emit_all_ln output [`DIRECTIVE "class";   `WORD ci]
  | CD.Annot_Value annot -> emit_annotation output annot
  | CD.Array_Value av ->
      emit_ln output (`DIRECTIVE "array");
      indent output;
      List.iter (emit_annotation_element output) av;
      undent output;
      emit_all_ln output [`DIRECTIVE "end"; `WORD "array"]

and emit_annotation output ?typ (annot_class, fields) =
  emit output (`DIRECTIVE "annotation");
  Option.may (fun x -> emit output (`WORD x)) typ;
  emit_ln output (`WORD (JT.string_of_type annot_class));
  indent output;
  List.iter (fun (nm,v) ->
	       emit_all output [`DIRECTIVE "element"; `WORD nm];
	       emit_annotation_element output v) fields;
  undent output;
  emit_all_ln output [`DIRECTIVE "end"; `WORD "annotation"]

let emit_field output formatters field =
  emit output (`DIRECTIVE "field");
  emit_field_flags output field.CD.fd_flags;
  emit output (`WORD field.CD.fd_name);
  emit output (`WORD (JT.string_of_type field.CD.fd_ty));
  emit output `NEWLINE;
  indent output;
  Option.may (fun cv -> emit output (`DIRECTIVE "constantvalue"); emit_constant_value output cv; emit output `NEWLINE) field.CD.fd_constant_value;
  if field.CD.fd_deprecated then (emit_ln output (`DIRECTIVE "deprecated"));
  if field.CD.fd_synthetic then (emit_ln output (`DIRECTIVE "synthetic"));
  Option.may (fun signature -> emit_all_ln output [`DIRECTIVE "signature"; `STRINGLIT signature]) field.CD.fd_signature;
  List.iter (fun a -> emit_annotation output ~typ:"visible" a) field.CD.fd_visible_annotations;
  List.iter (fun a -> emit_annotation output ~typ:"invisible" a) field.CD.fd_invisible_annotations;
  emit_custom_attribute output formatters.format_field_attribute field.CD.fd_custom_attributes;
  List.iter (emit_generic_attribute output) field.CD.fd_generic_attributes;
  undent output;
  emit_all_ln output [`DIRECTIVE "end"; `WORD "field"]

let emit_instruction output line_number_table instr = match instr with
  | BC.Jlabel (l,_)    ->
      emit ~undent:1 output (`WORD (Label.to_string l ^ ":"));
      emit output `NEWLINE;
      if Hashtbl.mem line_number_table l then
	emit_all_ln output [`DIRECTIVE "line"; `INT (Hashtbl.find line_number_table l)]
  | BC.Jaaload         -> emit_ln output (`WORD "aaload")
  | BC.Jaastore        -> emit_ln output (`WORD "aastore")
  | BC.Jaconst_null    -> emit_ln output (`WORD "aconst_null")
  | BC.Jaload i        -> emit_all_ln output [`WORD "aload"; `INT i]
  | BC.Jarraylength    -> emit_ln output (`WORD "arraylength")
  | BC.Jastore i       -> emit_all_ln output [`WORD "astore"; `INT i]
  | BC.Jathrow         -> emit_ln output (`WORD "athrow")
  | BC.Jbaload         -> emit_ln output (`WORD "baload")
  | BC.Jbastore        -> emit_ln output (`WORD "bastore")
  | BC.Jcaload         -> emit_ln output (`WORD "caload")
  | BC.Jcastore        -> emit_ln output (`WORD "castore")
  | BC.Jcheckcast ty   -> emit_all_ln output [`WORD "checkcast"; `WORD (JT.string_of_reftype ty)]
  | BC.Jclassconst ty  -> emit_all_ln output [`WORD "classconst"; `WORD (JT.string_of_reftype ty)]
  | BC.Jd2f            -> emit_ln output (`WORD "d2f")
  | BC.Jd2i            -> emit_ln output (`WORD "d2i")
  | BC.Jd2l            -> emit_ln output (`WORD "d2l")
  | BC.Jdadd           -> emit_ln output (`WORD "dadd")
  | BC.Jdaload         -> emit_ln output (`WORD "daload")
  | BC.Jdastore        -> emit_ln output (`WORD "dastore")
  | BC.Jdcmpg          -> emit_ln output (`WORD "dcmpg")
  | BC.Jdcmpl          -> emit_ln output (`WORD "dcmpl")
  | BC.Jdconst d       -> emit_all_ln output [`WORD "dconst"; `DOUBLE d]
  | BC.Jddiv           -> emit_ln output (`WORD "ddiv")
  | BC.Jdload i        -> emit_all_ln output [`WORD"dload"; `INT i]
  | BC.Jdmul           -> emit_ln output (`WORD "dmul")
  | BC.Jdneg           -> emit_ln output (`WORD "dneg")
  | BC.Jdrem           -> emit_ln output (`WORD "drem")
  | BC.Jdstore i       -> emit_all_ln output [`WORD"dstore"; `INT i]
  | BC.Jdsub           -> emit_ln output (`WORD "dsub")
  | BC.Jdup            -> emit_ln output (`WORD "dup")
  | BC.Jdup_x1         -> emit_ln output (`WORD "dup_x1")
  | BC.Jdup_x2         -> emit_ln output (`WORD "dup_x2")
  | BC.Jdup2           -> emit_ln output (`WORD "dup2")
  | BC.Jdup2_x1        -> emit_ln output (`WORD "dup2_x1")
  | BC.Jdup2_x2        -> emit_ln output (`WORD "dup2_x2")
  | BC.Jf2d            -> emit_ln output (`WORD "f2d")
  | BC.Jf2i            -> emit_ln output (`WORD "f2i")
  | BC.Jf2l            -> emit_ln output (`WORD "f2l")
  | BC.Jfadd           -> emit_ln output (`WORD "fadd")
  | BC.Jfaload         -> emit_ln output (`WORD "faload")
  | BC.Jfastore        -> emit_ln output (`WORD "fastore")
  | BC.Jfcmpg          -> emit_ln output (`WORD "fcmpg")
  | BC.Jfcmpl          -> emit_ln output (`WORD "fcmpl")
  | BC.Jfconst f       -> emit_all_ln output [`WORD"fconst";`DOUBLE (JFloat.to_float f)]
  | BC.Jfdiv           -> emit_ln output (`WORD "fdiv")
  | BC.Jfload i        -> emit_all_ln output [`WORD"fload"; `INT i]
  | BC.Jfmul           -> emit_ln output (`WORD "fmul")
  | BC.Jfneg           -> emit_ln output (`WORD "fneg")
  | BC.Jfrem           -> emit_ln output (`WORD "frem")
  | BC.Jfstore i       -> emit_all_ln output [`WORD"fstore"; `INT i]
  | BC.Jfsub           -> emit_ln output (`WORD "fsub")
  | BC.Jgetfield (c,n,t)  -> emit_all_ln output [`WORD"getfield"; `WORD (JT.string_of_class c); `WORD n; `WORD (JT.string_of_type t)]
  | BC.Jgetstatic (c,n,t) -> emit_all_ln output [`WORD"getstatic"; `WORD (JT.string_of_class c); `WORD n; `WORD (JT.string_of_type t)]
  | BC.Jgoto l         -> emit_all_ln output [`WORD"goto"; `WORD (Label.to_string l)]
  | BC.Ji2b            -> emit_ln output (`WORD "i2b")
  | BC.Ji2c            -> emit_ln output (`WORD "i2c")
  | BC.Ji2d            -> emit_ln output (`WORD "i2d")
  | BC.Ji2f            -> emit_ln output (`WORD "i2f")
  | BC.Ji2l            -> emit_ln output (`WORD "i2l")
  | BC.Ji2s            -> emit_ln output (`WORD "i2s")
  | BC.Jiadd           -> emit_ln output (`WORD "iadd")
  | BC.Jiaload         -> emit_ln output (`WORD "iaload")
  | BC.Jiand           -> emit_ln output (`WORD "iand")
  | BC.Jiastore        -> emit_ln output (`WORD "iastore")
  | BC.Jiconst i       -> emit_all_ln output [`WORD"iconst"; `INT32 i]
  | BC.Jidiv           -> emit_ln output (`WORD "idiv")
  | BC.Jif_acmpeq l    -> emit_all_ln output [`WORD"if_acmpeq";`WORD (Label.to_string l)]
  | BC.Jif_acmpne l    -> emit_all_ln output [`WORD"if_acmpne";`WORD (Label.to_string l)]
  | BC.Jif_icmpeq l    -> emit_all_ln output [`WORD"if_icmpeq";`WORD (Label.to_string l)]
  | BC.Jif_icmpne l    -> emit_all_ln output [`WORD"if_icmpne";`WORD (Label.to_string l)]
  | BC.Jif_icmplt l    -> emit_all_ln output [`WORD"if_icmplt";`WORD (Label.to_string l)]
  | BC.Jif_icmpge l    -> emit_all_ln output [`WORD"if_icmpge";`WORD (Label.to_string l)]
  | BC.Jif_icmpgt l    -> emit_all_ln output [`WORD"if_icmpgt";`WORD (Label.to_string l)]
  | BC.Jif_icmple l    -> emit_all_ln output [`WORD"if_icmple";`WORD (Label.to_string l)]
  | BC.Jifeq l         -> emit_all_ln output [`WORD"ifeq";`WORD (Label.to_string l)]
  | BC.Jifne l         -> emit_all_ln output [`WORD"ifne";`WORD (Label.to_string l)]
  | BC.Jiflt l         -> emit_all_ln output [`WORD"iflt";`WORD (Label.to_string l)]
  | BC.Jifge l         -> emit_all_ln output [`WORD"ifge";`WORD (Label.to_string l)]
  | BC.Jifgt l         -> emit_all_ln output [`WORD"ifgt";`WORD (Label.to_string l)]
  | BC.Jifle l         -> emit_all_ln output [`WORD"ifle";`WORD (Label.to_string l)]
  | BC.Jifnonnull l    -> emit_all_ln output [`WORD"ifnonnull";`WORD (Label.to_string l)]
  | BC.Jifnull l       -> emit_all_ln output [`WORD"ifnull";`WORD (Label.to_string l)]
  | BC.Jiinc (a,b)     -> emit_all_ln output [`WORD"iinc"; `INT a; `INT b]
  | BC.Jiload i        -> emit_all_ln output [`WORD"iload"; `INT i]
  | BC.Jimul           -> emit_ln output (`WORD "imul")
  | BC.Jineg           -> emit_ln output (`WORD "ineg")
  | BC.Jinstanceof ty  -> emit_all_ln output [`WORD"instanceof"; `WORD (JT.string_of_reftype ty)]
  | BC.Jinvokeinterface (c,n,s) -> emit_all_ln output [`WORD"invokeinterface";`WORD(JT.string_of_class c);`WORD n;`WORD (JT.string_of_methodsig s)]
  | BC.Jinvokespecial (c,n,s)   -> emit_all_ln output [`WORD"invokespecial";`WORD(JT.string_of_reftype c);`WORD n;`WORD (JT.string_of_methodsig s)]
  | BC.Jinvokestatic (c,n,s)    -> emit_all_ln output [`WORD"invokestatic";`WORD(JT.string_of_reftype c);`WORD n;`WORD (JT.string_of_methodsig s)]
  | BC.Jinvokevirtual (c,n,s)   -> emit_all_ln output [`WORD"invokevirtual";`WORD(JT.string_of_reftype c);`WORD n;`WORD (JT.string_of_methodsig s)]
  | BC.Jior            -> emit_ln output (`WORD "ior")
  | BC.Jirem           -> emit_ln output (`WORD "irem")
  | BC.Jishl           -> emit_ln output (`WORD "ishl")
  | BC.Jishr           -> emit_ln output (`WORD "ishr")
  | BC.Jistore i       -> emit_all_ln output [`WORD"istore"; `INT i]
  | BC.Jisub           -> emit_ln output (`WORD "isub")
  | BC.Jiushr          -> emit_ln output (`WORD "iushr")
  | BC.Jixor           -> emit_ln output (`WORD "ixor")
  | BC.Jjsr l          -> emit_all_ln output [`WORD"jsr"; `WORD (Label.to_string l)]
  | BC.Jl2d            -> emit_ln output (`WORD "l2d")
  | BC.Jl2f            -> emit_ln output (`WORD "l2f")
  | BC.Jl2i            -> emit_ln output (`WORD "l2i")
  | BC.Jladd           -> emit_ln output (`WORD "ladd")
  | BC.Jlaload         -> emit_ln output (`WORD "laload")
  | BC.Jland           -> emit_ln output (`WORD "land")
  | BC.Jlastore        -> emit_ln output (`WORD "lastore")
  | BC.Jlcmp           -> emit_ln output (`WORD "lcmp")
  | BC.Jlconst i       -> emit_all_ln output [`WORD"lconst"; `INT64 i]
  | BC.Jldiv           -> emit_ln output (`WORD "ldiv")
  | BC.Jlload i        -> emit_all_ln output [`WORD"lload"; `INT i]
  | BC.Jlmul           -> emit_ln output (`WORD "lmul")
  | BC.Jlneg           -> emit_ln output (`WORD "lneg")
  | BC.Jlookupswitch (default, jumps) ->
      emit_ln output (`WORD "lookupswitch");
      indent output;
      List.iter (fun (n,l) -> emit_all_ln output [`INT32 n; `WORD ":"; `WORD (Label.to_string l)]) jumps;
      emit_all_ln output [`WORD"default"; `WORD":"; `WORD (Label.to_string default)];
      undent output
  | BC.Jlor            -> emit_ln output (`WORD "lor")
  | BC.Jlrem           -> emit_ln output (`WORD "lrem")
  | BC.Jlshl           -> emit_ln output (`WORD "lshl")
  | BC.Jlshr           -> emit_ln output (`WORD "lshr")
  | BC.Jlstore i       -> emit_all_ln output [`WORD"lstore"; `INT i]
  | BC.Jlsub           -> emit_ln output (`WORD "lsub")
  | BC.Jlushr          -> emit_ln output (`WORD "lushr")
  | BC.Jlxor           -> emit_ln output (`WORD "lxor")
  | BC.Jmonitorenter   -> emit_ln output (`WORD "monitorenter")
  | BC.Jmonitorexit    -> emit_ln output (`WORD "monitorexit")
  | BC.Jnew c          -> emit_all_ln output [`WORD"new"; `WORD (JT.string_of_class c)]
  | BC.Jnewarray (ty,dim) -> emit_all output [`WORD"newarray"; `WORD(JT.string_of_type ty); `INT dim]
  | BC.Jnop            -> emit_ln output (`WORD "nop")
  | BC.Jpop            -> emit_ln output (`WORD "pop")
  | BC.Jpop2           -> emit_ln output (`WORD "pop2")
  | BC.Jputfield (c,n,t)  -> emit_all_ln output [`WORD"putfield";`WORD (JT.string_of_class c);`WORD n;`WORD (JT.string_of_type t)]
  | BC.Jputstatic (c,n,t) -> emit_all_ln output [`WORD"putstatic";`WORD (JT.string_of_class c);`WORD n;`WORD (JT.string_of_type t)]
  | BC.Jret l          -> emit_all_ln output [`WORD"ret"; `INT l]
  | BC.Jreturn         -> emit_ln output (`WORD "return")
  | BC.Jsaload         -> emit_ln output (`WORD "saload")
  | BC.Jsastore        -> emit_ln output (`WORD "sastore")
  | BC.Jsconst s       -> emit_all_ln output [`WORD"sconst"; `STRINGLIT s]
  | BC.Jswap           -> emit_ln output (`WORD "swap")
  | BC.Jtableswitch (default, low, labels) ->
      emit_all_ln output [`WORD"tableswitch"; `INT32 low];
      indent output;
      List.iter (fun l -> emit_ln output (`WORD (Label.to_string l))) labels;
      emit_all_ln output [`WORD "default:"; `WORD (Label.to_string default)];
      undent output

let emit_exception_handler output hdl =
  emit_all_ln output
    [ `DIRECTIVE "catch"
    ; `WORD (Option.map_default JT.string_of_class "any" hdl.CD.exn_catch)
    ; `WORD "from"
    ; `WORD (Label.to_string hdl.CD.exn_start)
    ; `WORD "to"
    ; `WORD (Label.to_string hdl.CD.exn_end)
    ; `WORD "using"
    ; `WORD (Label.to_string hdl.CD.exn_entry)
    ]

(*let render_localvar output localvar =
  printf output "    .var %d is %s %s from %s to %s\n"
    localvar.CD.lv_index
    localvar.CD.lv_name
    (JT.string_of_type localvar.CD.lv_ty)
    (Label.to_string localvar.CD.lv_from)
    (Label.to_string localvar.CD.lv_thru)*)

let add_lineno table line_number_info =
  Hashtbl.add table line_number_info.CD.ln_start line_number_info.CD.ln_line

let emit_code output formatters code =
  let line_num_table = Hashtbl.create 10 in
    Option.may (List.iter (add_lineno line_num_table)) code.CD.code_line_numbers;
    emit_ln output (`DIRECTIVE "code");
    indent output;
    emit_all_ln output [`DIRECTIVE "max_stack"; `WORD (Printf.sprintf "%d" code.CD.code_max_stack)];
    emit_all_ln output [`DIRECTIVE "locals"; `WORD (Printf.sprintf "%d" code.CD.code_locals)];
    emit output `NEWLINE;
    List.iter (emit_exception_handler output)     code.CD.code_handlers;
    List.iter (emit_instruction output line_num_table) code.CD.code_code;
    (* FIXME: integrate localvars, localvartype into the code itself, next to the labels *)
    (* FIXME: do stack maps *)
    emit_custom_attribute output (formatters.format_code_attribute Label.to_string) code.CD.code_custom_attributes;
    List.iter (emit_generic_attribute output) code.CD.code_generic_attributes;
    undent output;
    emit_all_ln output [`DIRECTIVE "end"; `WORD "code"]

let emit_method_flags output flags =
  let (+>) b s = if b then emit output (`WORD s) in
    flags.AF.m_public       +> "public";
    flags.AF.m_private      +> "private";
    flags.AF.m_protected    +> "protected";
    flags.AF.m_static       +> "static";
    flags.AF.m_final        +> "final";
    flags.AF.m_synchronized +> "synchronized";
    flags.AF.m_bridge       +> "bridge";
    flags.AF.m_varargs      +> "varargs";
    flags.AF.m_native       +> "native";
    flags.AF.m_abstract     +> "abstract";
    flags.AF.m_strictfp     +> "strictfp";
    flags.AF.m_synthetic    +> "synthetic"

let emit_annotation_default output value =
  emit_all_ln output [`DIRECTIVE "annotation"; `WORD "default"];
  indent output;
  emit_annotation_element output value;
  undent output;
  emit_all_ln output [`DIRECTIVE "end"; `WORD "annotation"]

let emit_method output formatters meth =
  emit output (`DIRECTIVE "method");
  emit_method_flags output meth.CD.md_flags;
  emit_all_ln output [ `WORD meth.CD.md_name
		     ; `WORD (JT.string_of_methodsig meth.CD.md_sig)
		     ];
  indent output;
  List.iter (fun cl -> emit_all_ln output [`DIRECTIVE"throws";`WORD (JT.string_of_class cl)]) meth.CD.md_exceptions;
  if meth.CD.md_deprecated then (emit_ln output (`DIRECTIVE "deprecated"));
  if meth.CD.md_synthetic then (emit_ln output (`DIRECTIVE "synthetic"));
  Option.may (fun signature -> emit_all_ln output [`DIRECTIVE "signature"; `STRINGLIT signature]) meth.CD.md_signature;
  List.iter (fun a -> emit_annotation output ~typ:"visible" a) meth.CD.md_visible_annotations;
  List.iter (fun a -> emit_annotation output ~typ:"invisible" a) meth.CD.md_invisible_annotations;
  List.iteri (fun i -> List.iter (emit_annotation output ~typ:(Printf.sprintf "visibleparam %d" i))) meth.CD.md_visible_param_annotations;
  List.iteri (fun i -> List.iter (emit_annotation output ~typ:(Printf.sprintf "invisibleparam %d" i))) meth.CD.md_invisible_param_annotations;
  Option.may (emit_code output formatters) meth.CD.md_code;
  Option.may (emit_annotation_default output) meth.CD.md_annotation_default;
  emit_custom_attribute output formatters.format_method_attribute meth.CD.md_custom_attributes;
  List.iter (emit_generic_attribute output) meth.CD.md_generic_attributes;
  undent output;
  emit_all_ln output [`DIRECTIVE "end"; `WORD "method"]

let emit_class_flags output flags =
  let (+>) b s = if b then emit output (`WORD s) in
    flags.AF.c_public +> "public";
    flags.AF.c_private +> "private";
    flags.AF.c_protected +> "protected";
    flags.AF.c_static +> "static";
    flags.AF.c_final +> "final";
    flags.AF.c_super +> "super";
    (* interface is done separately *)
    flags.AF.c_abstract +> "abstract";
    flags.AF.c_synthetic +> "synthetic";
    flags.AF.c_annotation +> "annotation"; (* FIXME: should be done separately *)
    flags.AF.c_enum +> "enum" (* and this *)

let emit_enclosing_method output enc_method =
  emit_all output [ `DIRECTIVE "enclosing"
		  ; `WORD "method"
		  ; `WORD (Jvmtype.string_of_class enc_method.CD.ec_class)
		  ];
  Option.may (fun (nm, msig) -> emit_all output [`WORD nm; `WORD (Jvmtype.string_of_methodsig msig)]) enc_method.CD.ec_method;
  emit output `NEWLINE

let emit_newline output =
  emit output `NEWLINE

(* FIXME: do other attributes -- inner classes *)
let emit_classdecl output formatters cd =
  emit_all_ln output [`DIRECTIVE "bytecode"; `WORD (Printf.sprintf "%d.%d" cd.CD.major cd.CD.minor)];
  Option.may (fun s -> emit_all_ln output [`DIRECTIVE"source"; `STRINGLIT s]) cd.CD.srcfile;
  emit output (`DIRECTIVE (if cd.CD.flags.AF.c_interface then "interface" else "class"));
  emit_class_flags output cd.CD.flags;
  emit_ln output (`WORD (JT.string_of_class cd.CD.this));
  Option.may (fun super -> emit_all_ln output [`DIRECTIVE "super"; `WORD (JT.string_of_class super)]) cd.CD.super;
  List.iter (fun interface -> emit_all_ln output [`DIRECTIVE "implements"; `WORD (JT.string_of_class interface)]) cd.CD.interfaces;
  if cd.CD.deprecated then emit_ln output (`DIRECTIVE "deprecated");
  if cd.CD.synthetic then emit_ln output (`DIRECTIVE "synthetic");
  Option.may (emit_enclosing_method output) cd.CD.enclosing_method;
  Option.may (fun s -> emit_all_ln output [`DIRECTIVE"debug";`STRINGLIT s]) cd.CD.source_debug_extn;  
  Option.may (fun signature -> emit_all_ln output [`DIRECTIVE "signature"; `STRINGLIT signature]) cd.CD.signature;
  List.iter (fun x -> emit_newline output; emit_annotation output ~typ:"visible" x) cd.CD.visible_annotations;
  List.iter (fun x -> emit_newline output; emit_annotation output ~typ:"invisible" x) cd.CD.invisible_annotations;
  emit_custom_attribute output formatters.format_class_attribute cd.CD.custom_attributes;
  List.iter (fun x -> emit_newline output; emit_generic_attribute output x) cd.CD.generic_attributes;
  List.iter (fun x -> emit_newline output; emit_field output formatters x) cd.CD.fields;
  List.iter (fun x -> emit_newline output; emit_method output formatters x) cd.CD.methods

let () =
  let cf       = ClassfileInput.read_classfile (IO.input_channel stdin) in
  let cd       = Decompile.decompile cf Decompile.null_attribute_decompilers in
  let output   = IO.output_channel stdout in
  let _        = emit_classdecl (make_output output) null_formatters cd in
    ()

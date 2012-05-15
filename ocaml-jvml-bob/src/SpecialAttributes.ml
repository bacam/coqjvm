module CP = Constpool
module JT = Jvmtype

let split s =
  let rec next i l =
    try
      let j = String.index_from s i ';' in
      let k =
	try String.index_from s (j+1) ';'
	with Not_found -> String.length s
      in
      next (k+1) ((String.sub s i (j-i), String.sub s (j+1) (k-j-1))::l)
    with
	Not_found | Invalid_argument _ -> List.rev l
  in next 0 []

let parse_pcmap s get_label =
  let lpairs = split s in
  let pairs = List.map (fun (l,v) -> (get_label l, v)) lpairs in
  pairs

let pcmap_to_string lpairs get_label =
  let spairs = List.map (fun (pc,v) -> (get_label pc) ^ ";" ^ v) lpairs in
  String.concat ";" spairs

let pcmap_to_string_hash lpairs _ labels =
  pcmap_to_string lpairs (fun pc -> string_of_int (Hashtbl.find labels pc))

(* For the Constant Pool Additional attributes we need to store enough
   information to find the index of the corresponding constant pool
   entry. The methods have an extra string to hold the
   specification. *)
type cpaentry =
  | CPAE_static_method of Jvmtype.jref_type * string * Jvmtype.methodsig * string
  | CPAE_static_field of Jvmtype.jclass * string * Jvmtype.jtype
  | CPAE_instantiable_class of Jvmtype.jref_type
  | CPAE_instance_field of Jvmtype.jclass * string * Jvmtype.jtype
  | CPAE_instance_method of Jvmtype.jref_type * string * Jvmtype.methodsig * string
  | CPAE_instance_special_method of Jvmtype.jref_type * string * Jvmtype.methodsig * string
  | CPAE_classref of Jvmtype.jref_type

type class_attr =
  | CPA of cpaentry list
  | Class_Other of string * string

type code_attr =
  | Certificate of (Label.label * string) list
  | Code_Other of string * string

let decode_cpa pool attr =
  let pairs = split attr in
  List.map (fun (idxstring,content) ->
    let idx = CP.index_of_int (int_of_string idxstring) in
    let attrtype = String.sub content 0 2 in
    let spec = String.sub content 2 ((String.length content)-2) in
    match attrtype with
      | "sm" -> let (a,b,c) = CP.lookup_methodref pool idx in CPAE_static_method (a,b,c,spec)
      | "sf" -> let (a,b,c) = CP.lookup_fieldref pool idx in CPAE_static_field (a,b,c)
      | "ic" -> CPAE_instantiable_class (CP.lookup_class pool idx)
      | "if" -> let (a,b,c) = CP.lookup_fieldref pool idx in CPAE_instance_field (a,b,c)
      | "im" -> let (a,b,c) = CP.lookup_methodref pool idx in CPAE_instance_method (a,b,c,spec)
      | "is" -> let (a,b,c) = CP.lookup_methodref pool idx in CPAE_instance_special_method (a,b,c,spec)
      | "cr" -> CPAE_classref (CP.lookup_class pool idx)
      | x -> failwith ("Unrecognised CPA entry: " ^ x)) pairs

let methodref_of_string s =
  let check = function Some v -> v | None -> failwith ("Unable to parse CPA methodref: " ^ s) in
  let i = String.index s ' ' in
  let j = String.index_from s (i+1) ' ' in
  (check (JT.reftype_of_string (String.sub s 0 i)),
   String.sub s (i+1) (j-i-1),
   check (JT.methodsig_of_string (String.sub s (j+1) ((String.length s)-j-1))))

let fieldref_of_string s =
  let check = function Some v -> v | None -> failwith ("Unable to parse CPA fieldref: " ^ s) in
  let i = String.index s ' ' in
  let j = String.index_from s (i+1) ' ' in
  (check (JT.class_of_string (String.sub s 0 i)),
   String.sub s (i+1) (j-i-1),
   check (JT.type_of_string (String.sub s (j+1) ((String.length s)-j-1))))

let parse_cpa attr =
  let pairs = split attr in
  List.map (fun (id,content) ->
    let attrtype = String.sub content 0 2 in
    let spec = String.sub content 2 ((String.length content)-2) in
    let checkcr = function Some v -> v | None -> failwith ("Unable to parse CPA classref: " ^ id) in
    match attrtype with
      | "sm" -> let (a,b,c) = methodref_of_string id in CPAE_static_method (a,b,c,spec)
      | "sf" -> let (a,b,c) = fieldref_of_string id in CPAE_static_field (a,b,c)
      | "ic" -> CPAE_instantiable_class (checkcr (JT.reftype_of_string id))
      | "if" -> let (a,b,c) = fieldref_of_string id in CPAE_instance_field (a,b,c)
      | "im" -> let (a,b,c) = methodref_of_string id in CPAE_instance_method (a,b,c,spec)
      | "is" -> let (a,b,c) = methodref_of_string id in CPAE_instance_special_method (a,b,c,spec)
      | "cr" -> CPAE_classref (checkcr (JT.reftype_of_string id))
      | x -> failwith ("Unrecognised CPA entry: " ^ x)) pairs

let compile_cpa cpbuilder entries =
  let string_of_index idx = string_of_int (CP.index_to_int idx) in
  let pairs = List.map (function
    | CPAE_static_method (a,b,c,spec) -> (string_of_index (CP.add_method_ref cpbuilder (a,b,c))) ^ ";sm" ^ spec
    | CPAE_static_field (cl,fl,fty) -> (string_of_index (CP.add_field_ref cpbuilder (cl,fl,fty))) ^ ";sf"
    | CPAE_instantiable_class ty -> (string_of_index (CP.add_class cpbuilder ty)) ^ ";ic"
    | CPAE_instance_field (cl,fl,fty) -> (string_of_index (CP.add_field_ref cpbuilder (cl,fl,fty))) ^ ";if"
    | CPAE_instance_method (a,b,c,spec) -> (string_of_index (CP.add_method_ref cpbuilder (a,b,c))) ^ ";im" ^ spec
    | CPAE_instance_special_method (a,b,c,spec) -> (string_of_index (CP.add_method_ref cpbuilder (a,b,c))) ^ ";is" ^ spec
    | CPAE_classref ty -> (string_of_index (CP.add_class cpbuilder ty)) ^ ";cr") entries
  in String.concat ";" pairs


let code_parser (name,attr) get_label =
  match name with
    | "uk.ac.ed.inf.request.Certificate" -> Certificate (parse_pcmap attr get_label)
    | _ -> Code_Other (name,attr)

let class_parser (name,attr) =
  match name with
    | "uk.ac.ed.inf.request.ConstantPoolAdditional" -> CPA (parse_cpa attr)
    | _ -> Class_Other (name,attr)

let id x = x

type ('f,'m,'c,'cl) attribute_parsers = {
  (* NB: at the time of writing the assembler doesn't handle field attributes. *)
  parse_field_attribute  : string * string -> 'f;
  parse_method_attribute : string * string -> 'm;
  parse_code_attribute   : string * string -> (string -> Label.label) -> 'c;
  parse_class_attribute  : string * string -> 'cl;
}

let parsers = {
  parse_field_attribute  = id;
  parse_method_attribute = id;
  parse_code_attribute   = code_parser;
  parse_class_attribute  = class_parser;
}

let code_compiler attr cpbuilder labels =
  match attr with
    | Certificate v -> ("uk.ac.ed.inf.request.Certificate", pcmap_to_string_hash v cpbuilder labels)
    | Code_Other (n,v) -> (n,v)

let class_compiler attr cpbuilder =
  match attr with
    | CPA entries -> ("uk.ac.ed.inf.request.ConstantPoolAdditional", compile_cpa cpbuilder entries)
    | Class_Other (n,v) -> (n,v)

let compilers = {
  Compile.generic_attribute_compilers with
  Compile.compile_code_attribute = code_compiler;
  Compile.compile_class_attribute = class_compiler;
}

let to_string_code get_label attr =
  match attr with
    | Certificate v -> ("uk.ac.ed.inf.request.Certificate", pcmap_to_string v get_label)
    | Code_Other (n,v) -> (n,v)

let class_decompiler (name,s) pool =
  match name with
    | "uk.ac.ed.inf.request.ConstantPoolAdditional" -> CPA (decode_cpa pool s)
    | _ -> Class_Other (name,s)

let meth_to_string (clty, mth, msg) =
  (JT.string_of_reftype clty) ^ " " ^ mth ^ " " ^ (JT.string_of_methodsig msg)

let field_to_string (cl,fl,fty) =
  (JT.string_of_class cl) ^ " " ^ fl ^ " " ^ (JT.string_of_type fty)

let cpa_to_string entries =
  let pairs = List.map (function
    | CPAE_static_method (a,b,c,spec) -> (meth_to_string (a,b,c)) ^ ";sm" ^ spec
    | CPAE_static_field (cl,fl,fty) -> (field_to_string (cl,fl,fty)) ^ ";sf"
    | CPAE_instantiable_class ty -> (JT.string_of_reftype ty) ^ ";ic"
    | CPAE_instance_field (cl,fl,fty) -> (field_to_string (cl,fl,fty)) ^ ";if"
    | CPAE_instance_method (a,b,c,spec) -> (meth_to_string (a,b,c)) ^ ";im" ^ spec
    | CPAE_instance_special_method (a,b,c,spec) -> (meth_to_string (a,b,c)) ^ ";is" ^ spec
    | CPAE_classref ty -> (JT.string_of_reftype ty) ^ ";cr") entries
  in String.concat ";" pairs

let to_string_class attr =
  match attr with
    | CPA entries -> ("uk.ac.ed.inf.request.ConstantPoolAdditional", cpa_to_string entries)
    | Class_Other (name,s) -> (name,s)

let code_decompiler (name,s) pool gl =
  match name with
    | "uk.ac.ed.inf.request.Certificate" -> Certificate (parse_pcmap s (fun l -> gl (int_of_string l)))
    | _ -> Code_Other (name,s)

let decompilers = {
  Decompile.generic_attribute_decompilers with
  Decompile.decompile_code_attribute  = code_decompiler;
  Decompile.decompile_class_attribute = class_decompiler;
}

type ('f,'m,'c,'cl) attribute_formatters = {
  format_field_attribute  : 'f -> string * string;
  format_method_attribute : 'm -> string * string;
  format_code_attribute   : (Label.label -> string) -> 'c -> string * string;
  format_class_attribute  : 'cl -> string * string;
}

let formatters = {
  format_field_attribute  = id;
  format_method_attribute = id;
  format_code_attribute   = to_string_code;
  format_class_attribute  = to_string_class;
}

module JT = Jvmtype
module CD = Classdecl
module CF = Classfile
module CP = Constpool

open ExtString

exception SignatureError of string

type method_info =
    { method_name  : string
    ; method_sig   : JT.methodsig
    ; method_annot : CD.annotation list
      (* + flags *)
    }

type field_info =
    { field_name  : string
    ; field_annot : CD.annotation list
    ; field_type  : JT.jtype
      (* + flags *)
    }

type class_info =
    { class_name       : JT.jclass
    ; class_super      : JT.jclass option
    ; class_interfaces : JT.jclass list
    ; class_annot      : CD.annotation list
    ; class_fields     : field_info list
    ; class_methods    : method_info list
      (* + flags *)
    }

(* *)

let lookup_utf8 pool idx = match CP.lookup pool idx with
  | CP.CPutf8 s -> s
  | _           -> raise (SignatureError "bad link to utf8")

let lookup_class pool idx = match CP.lookup pool idx with
  | CP.CPclass idx -> (match JT.class_of_string (lookup_utf8 pool idx) with
			 | Some c -> c
			 | None -> raise (SignatureError "Invalid class name"))
  | _              -> raise (SignatureError "bad link to class_info")

let lookup_methodsig pool idx = match JT.methodsig_of_string (lookup_utf8 pool idx) with
  | None    -> raise (SignatureError "Invalid method signature")
  | Some ms -> ms

let lookup_type pool idx = match JT.type_of_string (lookup_utf8 pool idx) with
  | None   -> raise (SignatureError "Invalid type")
  | Some t -> t

let rec decompile_element pool element = match element with
  | CF.Const_Value (CF.String, idx)  -> CD.Const_Value (CD.String (lookup_utf8 pool idx))
  | CF.Const_Value (_, idx)          -> assert false (* FIXME *)
  | CF.Enum_Const_Value (idx1, idx2) -> CD.Enum_Const_Value (lookup_utf8 pool idx1, lookup_utf8 pool idx2)
  | CF.Class_Info idx                -> CD.Class_Info (lookup_utf8 pool idx)
  | CF.Annot_Value annot             -> CD.Annot_Value (decompile_annotation pool annot)
  | CF.Array_Value elements          -> CD.Array_Value (List.map (decompile_element pool) elements)

and decompile_element_pair pool (name_idx, element) =
  (lookup_utf8 pool name_idx, decompile_element pool element)

and decompile_annotation pool (type_idx, elements) =
  let annot_type = lookup_utf8 pool type_idx in
  let elements = List.map (decompile_element_pair pool) elements in
    (annot_type, elements)

let rec extract_annotations pool annots_accum attrs = match attrs with
  | CF.Attribute (_, CF.Attr_RuntimeVisibleAnnotations annots)::attrs ->
      let annots' = List.map (decompile_annotation pool) annots in
	extract_annotations pool (annots' @ annots_accum) attrs
  | CF.Attribute (_, CF.Attr_RuntimeInvisibleAnnotations annots)::attrs ->
      let annots' = List.map (decompile_annotation pool) annots in
	extract_annotations pool (annots' @ annots_accum) attrs
  | [] ->
      List.rev annots_accum
  | _::attrs ->
      extract_annotations pool annots_accum attrs

let method_info_from_classfile pool mem =
  let name   = lookup_utf8 pool mem.CF.m_name in
  let desc   = lookup_methodsig pool mem.CF.m_desc in
  let annots = extract_annotations pool [] mem.CF.m_attrs in
    { method_name  = name
    ; method_sig   = desc
    ; method_annot = annots
    }

let field_info_from_classfile pool mem =
  let name   = lookup_utf8 pool mem.CF.m_name in
  let typ    = lookup_type pool mem.CF.m_desc in
  let annots = extract_annotations pool [] mem.CF.m_attrs in
    { field_name  = name
    ; field_type  = typ
    ; field_annot = annots
    }

(* this is really a mini decompile function *)
let classinfo_from_classfile cf =
  let pool       = cf.CF.pool in
  let name       = lookup_class pool cf.CF.this in
  let super      = Option.map (lookup_class pool) cf.CF.super in
  let interfaces = List.map (lookup_class pool) cf.CF.ifcs in
  let annots     = extract_annotations pool [] cf.CF.attrs in
  let methods    = List.map (method_info_from_classfile pool) cf.CF.methods in
  let fields     = List.map (field_info_from_classfile pool) cf.CF.fields in
    { class_name       = name
    ; class_super      = super
    ; class_annot      = annots
    ; class_fields     = fields
    ; class_methods    = methods
    ; class_interfaces = interfaces
    }

(* FIXME: worry about windows later *)
let class_name_to_path (packages, class_name) =
  if packages = [] then
    class_name ^ ".class"
  else
    String.concat "/" packages ^ "/" ^ class_name ^ ".class"

type jarfile_info =
    {         jarfile_path   : string
    ; mutable jarfile_handle : Zipfile.zipfile option
    }
(* FIXME: need an operation to close all the handles *)

type search_path_component =
  | Jarfile   of jarfile_info
  | Directory of string

type signature_info =
    { sig_searchpaths : search_path_component list
    ; sig_classes     : (JT.jclass,class_info) Hashtbl.t
    }

let make_signature paths =
  let make_search_path_component path =
    if String.ends_with path ".jar" (* FIXME: should we do something more thorough here? *)
    then Jarfile { jarfile_path = path; jarfile_handle = None }
    else Directory path
  in
    { sig_searchpaths = List.map make_search_path_component paths
    ; sig_classes     = Hashtbl.create 20
    }

(* Following two functions need more error handling:
   - check that loaded class has the right name
   - catch and wrap errors from Zipfile
   - catch and wrap errors from ClassfileInput
   - catch and wrap errors from IO
   - catch and wrap errors from Decompilation
*)
let search_jarfile info class_name =
  let jarfile = (match info.jarfile_handle with
		   | None ->
		       let handle = Zipfile.open_in info.jarfile_path in
			 info.jarfile_handle <- Some handle;
			 handle
		   | Some handle ->
		       handle) in
  let class_name_as_path = class_name_to_path class_name in
    match Zipfile.find jarfile class_name_as_path with
      | None -> None
      | Some entry ->
	  let input     = Zipfile.open_entry jarfile entry in
	  let cf        = ClassfileInput.read_classfile input in
	  let ()        = IO.close_in input in
	  let classinfo = classinfo_from_classfile cf in
	    Some classinfo (* FIXME: more error handling *)

let search_directory path class_name =
  let fullpath = Filename.concat path (class_name_to_path class_name) in
    try
      let stat = Unix.stat fullpath in
	match stat.Unix.st_kind with
	  | Unix.S_REG ->
	      let cf = ClassfileInput.of_file fullpath in
		Some (classinfo_from_classfile cf)
	  | _ ->
	      None
    with
      | Unix.Unix_error (Unix.ENOENT, _, _) -> None
	  (* FIXME: more error handling *)

let search_component class_name component = match component with
  | Jarfile info       -> search_jarfile info class_name
  | Directory filename -> search_directory filename class_name

let search_for_class signature class_name =
  match Util.find_first (search_component class_name) signature.sig_searchpaths with
    | None -> None
    | Some ci ->
	Hashtbl.add signature.sig_classes class_name ci;
	Some ci

let lookup_class signature class_name =
  try Some (Hashtbl.find signature.sig_classes class_name)
  with Not_found -> search_for_class signature class_name

let lookup_method signature class_name method_name method_sig =
  assert false

let lookup_field signature class_name field_name field_type =
  assert false



(* Also need:
   resolve_class
   resolve_method
   resolve_field

   these all work relative to a collection of import statements

   for use by the Typechecker to resolve all the method and field
   names in the sources.

   arse: need resolution of classes when adding the results of a
   source-code parse
*)

(* when we look up a class:
   - search for it in the sourcepath
   - search for it in the classpath

   while extracting the signature from a source file, we just use
   something that resolves a class against some import statements
   and checks its existence.
*)

module type Resolver = sig
  type t

  (* import a.b.c.* -- import everything in package a.b.c on demand
     import a.b.c.d -- import the class a.b.c.d

     inner classes?
     enums?
     static functions?
  *)

  type import_statement =
    | Import_wildcard of string list
    | Import_single   of string list * string

  val make_resolver : import_statement list -> t

  val resolve_class : t -> string -> Jvmtype.jclass

  val resolve_method : Jvmtype.jclass -> string -> Jvmtype.jtype list -> (Jvmtype.jclass * string * Jvmtype.methodsig)

  val resolve_field : Jvmtype.jclass -> string -> Jvmtype.jclass * string * Jvmtype.jtype
end

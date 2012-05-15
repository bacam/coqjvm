(* Conversion from Classdecl to Classfile *)

exception CompileError of string

type ('f,'m,'c,'cl) attribute_compilers =
    { compile_field_attribute  : 'f -> Constpool.builder -> (string * string) list
    ; compile_method_attribute : 'm -> Constpool.builder -> (string * string) list
    ; compile_code_attribute   : 'c -> Constpool.builder -> (Label.label, int) Hashtbl.t -> (string * string) list
    ; compile_class_attribute  : 'cl -> Constpool.builder -> (string * string) list
    }

let null_attribute_compilers =
  { compile_field_attribute  = (fun a _ -> [])
  ; compile_method_attribute = (fun a _ -> [])
  ; compile_code_attribute   = (fun a _ _ -> [])
  ; compile_class_attribute  = (fun a _ -> [])
  }

module CD = Classdecl
module CP = Constpool
module CF = Classfile
module AF = AccessFlags

let translate_label label_map label = 
  try Hashtbl.find label_map label
  with Not_found -> raise (CompileError "translate_label: label not found")

let is_ui16 i = 0 <= i && i <= 0xffff

let translate_exception_handler cp_builder label_map handler =
  { CF.exn_start = translate_label label_map handler.CD.exn_start
  ; CF.exn_end   = translate_label label_map handler.CD.exn_end
  ; CF.exn_pc    = translate_label label_map handler.CD.exn_entry
  ; CF.exn_type  = Option.map (CP.add_class cp_builder) (Option.map (fun x -> Jvmtype.TObject x) handler.CD.exn_catch)
  }

let translate_linenumber_infos cp_builder label_map lnuminfos =
  let translate_linenumber_info lnuminfo =
    if not (is_ui16 lnuminfo.CD.ln_line) then
      raise (CompileError (Printf.sprintf "translate_linenumber_info: line number %d out of range" lnuminfo.CD.ln_line));
    { CF.ln_start = translate_label label_map lnuminfo.CD.ln_start
    ; CF.ln_line  = lnuminfo.CD.ln_line
    }
  in
    CF.Attribute (CP.add_utf8 cp_builder "LineNumberTable",
		  CF.Attr_LineNumberTable (List.map translate_linenumber_info lnuminfos))

let translate_localvar_infos cp_builder label_map lvs =
  let translate_localvar_info lv =
    let start  = translate_label label_map lv.CD.lv_from in
    let length = translate_label label_map lv.CD.lv_thru - start in
    let index  = lv.CD.lv_index in
      if not (is_ui16 length) then raise (CompileError (Printf.sprintf "translate_localvar_info: length out of range: %d" length));
      if not (is_ui16 index) then raise (CompileError (Printf.sprintf "translate_localvar_info: index out of range: %d" index));
      { CF.lv_start  = start
      ; CF.lv_length = length
      ; CF.lv_name   = CP.add_utf8 cp_builder lv.CD.lv_name
      ; CF.lv_desc   = CP.add_utf8 cp_builder (Jvmtype.string_of_type lv.CD.lv_ty)
      ; CF.lv_index  = index
      }
  in
    CF.Attribute (CP.add_utf8 cp_builder "LocalVariableTable",
		  CF.Attr_LocalVariableTable (List.map translate_localvar_info lvs))

let translate_localvartypes_infos cp_builder label_map vs =
  let translate_localvartype_info l =
    let start  = translate_label label_map l.CD.vt_from in
    let length = translate_label label_map l.CD.vt_thru - start in
    let index  = l.CD.vt_index in
      if not (is_ui16 length) then raise (CompileError (Printf.sprintf "translate_localvartype_info: length out of range: %d" length));
      if not (is_ui16 index) then raise (CompileError (Printf.sprintf "translate_localvartype_info: index out of range: %d" index));
      { CF.vt_start  = start
      ; CF.vt_length = length
      ; CF.vt_name   = CP.add_utf8 cp_builder l.CD.vt_name
      ; CF.vt_sign   = CP.add_utf8 cp_builder l.CD.vt_sign
      ; CF.vt_index  = index
      }
  in
    CF.Attribute (CP.add_utf8 cp_builder "LocalVariableTypeTable",
		  CF.Attr_LocalVariableTypeTable (List.map translate_localvartype_info vs))

(* translating annotations *)
let rec translate_element cp_builder e = match e with
  | CD.Const_byte b   -> CF.Const_Value (CF.Byte, CP.add_int cp_builder (Int32.of_int b))
  | CD.Const_char c   -> CF.Const_Value (CF.Char, CP.add_int cp_builder c)
  | CD.Const_double d -> CF.Const_Value (CF.Double, CP.add_double cp_builder d)
  | CD.Const_float f  -> CF.Const_Value (CF.Float, CP.add_float cp_builder f)
  | CD.Const_int i    -> CF.Const_Value (CF.Int, CP.add_int cp_builder i)
  | CD.Const_long l   -> CF.Const_Value (CF.Long, CP.add_long cp_builder l)
  | CD.Const_short s  -> CF.Const_Value (CF.Short, CP.add_int cp_builder (Int32.of_int s))
  | CD.Const_bool b   -> CF.Const_Value (CF.Bool, CP.add_int cp_builder (Int32.of_int b))
  | CD.Const_string s -> CF.Const_Value (CF.String, CP.add_utf8 cp_builder s)
  | CD.Enum_Const_Value (t, c)
                      -> CF.Enum_Const_Value (CP.add_utf8 cp_builder (Jvmtype.string_of_class t), CP.add_utf8 cp_builder c)
  | CD.Class_Info s   -> CF.Class_Info (CP.add_utf8 cp_builder s)
  | CD.Annot_Value a  -> CF.Annot_Value (translate_annotation cp_builder a)
  | CD.Array_Value l  -> CF.Array_Value (List.map (translate_element cp_builder) l)
and translate_named_element cp_builder (name, value) =
  (CP.add_utf8 cp_builder name, translate_element cp_builder value)
and translate_annotation cp_builder (atype, values) =
  (CP.add_utf8 cp_builder (Jvmtype.string_of_type atype), List.map (translate_named_element cp_builder) values)

(* translating stackmaps *)
let translate_vtype_info cp_builder label_map v = match v with
  | CD.Top_vi                 -> CF.Top_vi
  | CD.Integer_vi             -> CF.Integer_vi
  | CD.Float_vi               -> CF.Float_vi
  | CD.Long_vi                -> CF.Long_vi
  | CD.Double_vi              -> CF.Double_vi
  | CD.Null_vi                -> CF.Null_vi
  | CD.UninitializedThis_vi   -> CF.UninitializedThis_vi
  | CD.Object_vi c            -> CF.Object_vi (CP.add_class cp_builder c)
  | CD.Uninitialized_vi label -> CF.Uninitialized_vi (translate_label label_map label)

(* FIXME: still untested *)
let translate_stackmaptable cp_builder label_map m =
  let translate_vt = translate_vtype_info cp_builder label_map in
  let rec process_frames frames prev acc = match frames with
    | [] -> List.rev acc
    | (label, frame)::frames ->
	let offset = translate_label label_map label in
	let delta  = offset - prev - 1 in
	  if delta < 0 then raise (CompileError "translate_stackmaptable: frames improperly ordered");
	  let frame' = match frame with
	    | CD.Same_frame             -> CF.Same_frame
	    | CD.Same_locals_1_stk item -> CF.Same_locals_1_stk (translate_vt item)
	    | CD.Chop_frame n when 1 <= n && n <= 3 -> CF.Chop_frame n
	    | CD.Chop_frame n           -> raise (CompileError (Printf.sprintf "translate_stackmaptable: invalid Chop_frame: %d" n))
	    | CD.Append_frame locals    ->
		let n = List.length locals in
		  if 1 <= n && n <= 3 then
		    CF.Append_frame (List.map translate_vt locals)
		  else
		    raise (CompileError (Printf.sprintf "translate_stackmaptable: invalid number of locals (%d) in Append_frame" n))
	    | CD.Full_frame (locals, stack) ->
		CF.Full_frame (List.map translate_vt locals,
			       List.map translate_vt stack)
	  in
	    process_frames frames offset ((delta, frame')::acc)
  in
    CF.Attribute (CP.add_utf8 cp_builder "StackMapTable",
		  CF.Attr_StackMapTable (process_frames m 0 []))

let translate_cldc_stackmaps cp_builder label_map frames =
  let translate_cldcstackframe (label, locals, stack) =
    let code_idx = translate_label label_map label in
    let locals'  = List.map (translate_vtype_info cp_builder label_map) locals in
    let stack'   = List.map (translate_vtype_info cp_builder label_map) stack in
      (code_idx, CF.CLDC_full_frame (locals', stack'))
  in
    CF.Attribute (CP.add_utf8 cp_builder "StackMap",
		  CF.Attr_StackMap (List.map translate_cldcstackframe frames))

let translate_generic_attrs cp_builder attrs =
  List.map (fun (name,data) -> 
	      CF.Attribute (CP.add_utf8 cp_builder name, CF.Attr data)) attrs

let translate_custom_attrs cp_builder attr_compiler attrs =
  translate_generic_attrs cp_builder (attr_compiler attrs cp_builder)

let translate_custom_code_attrs cp_builder label_map attr_compiler attrs =
  translate_generic_attrs cp_builder (attr_compiler attrs cp_builder label_map)

let add_const cp_builder const = match const with
  | CD.Cint i    -> CP.add_int cp_builder i
  | CD.Cfloat f  -> CP.add_float cp_builder f
  | CD.Clong l   -> CP.add_long cp_builder l
  | CD.Cdouble d -> CP.add_double cp_builder d
  | CD.Cstring s -> CP.add_string cp_builder s

let (+>) l x = match x with None -> l | Some x -> x::l

let translate_code cp_builder attribute_compiler return_ty code =
  let code', label_map =
    try CompileBytecode.compile_bytecode cp_builder return_ty code.CD.code_code
    with CompileBytecode.CompileBytecodeError s -> raise (CompileError s) in
  let handlers = List.map (translate_exception_handler cp_builder label_map) code.CD.code_handlers in
  let attributes =
    (translate_generic_attrs cp_builder code.CD.code_generic_attributes)
    @ (translate_custom_code_attrs cp_builder label_map attribute_compiler code.CD.code_custom_attributes)
    +> (Option.map (translate_linenumber_infos cp_builder label_map) code.CD.code_line_numbers) 
    +> (Option.map (translate_localvar_infos cp_builder label_map) code.CD.code_localvars)
    +> (Option.map (translate_localvartypes_infos cp_builder label_map) code.CD.code_localvartypes)
    +> (Option.map (translate_stackmaptable cp_builder label_map) code.CD.code_stackmap)
    +> (Option.map (translate_cldc_stackmaps cp_builder label_map) code.CD.code_cldc_stackmap)
  in
    if not (is_ui16 code.CD.code_max_stack) then raise (CompileError "max_stack out of range");
    if not (is_ui16 code.CD.code_locals) then raise (CompileError "locals out of range");
    CF.Attribute (CP.add_utf8 cp_builder "Code",
		  CF.Attr_Code (code.CD.code_max_stack,
				code.CD.code_locals,
				code',
				handlers,
				attributes))

let translate_exceptions cp_builder exns = match exns with
  | [] -> 
      None
  | exns ->
      Some (CF.Attribute (CP.add_utf8 cp_builder "Exceptions",
			  CF.Attr_Exceptions (List.map (fun x -> CP.add_class cp_builder (Jvmtype.TObject x)) exns)))

let translate_enclosing_method cp_builder r =
  CF.Attribute (CP.add_utf8 cp_builder "EnclosingMethod",
		CF.Attr_EnclosingMethod (CP.add_class cp_builder (Jvmtype.TObject r.CD.ec_class),
					 Option.map (CP.add_methoddesc cp_builder) r.CD.ec_method))

let translate_source_debug_extension cp_builder txt =
  CF.Attribute (CP.add_utf8 cp_builder "SourceDebugExtension",
		CF.Attr_SourceDebugExtension txt)
    
let translate_constant cp_builder value =
  CF.Attribute (CP.add_utf8 cp_builder "ConstantValue",
		CF.Attr_ConstantValue (add_const cp_builder value))


let translate_visible_annotations cp_builder annotations = match annotations with
  | [] -> None
  | annotations ->
      Some (CF.Attribute (CP.add_utf8 cp_builder "RuntimeVisibleAnnotations",
			  CF.Attr_RuntimeVisibleAnnotations (List.map (translate_annotation cp_builder) annotations)))

let translate_invisible_annotations cp_builder annotations = match annotations with
  | [] -> None
  | annotations ->
      Some (CF.Attribute (CP.add_utf8 cp_builder "RuntimeInvisibleAnnotations",
			  CF.Attr_RuntimeInvisibleAnnotations (List.map (translate_annotation cp_builder) annotations)))

let translate_deprecated cp_builder deprecated =
  if deprecated then
    Some (CF.Attribute (CP.add_utf8 cp_builder "Deprecated", CF.Attr_Deprecated))
  else
    None

let translate_synthetic cp_builder synthetic =
  if synthetic then
    Some (CF.Attribute (CP.add_utf8 cp_builder "Synthetic", CF.Attr_Synthetic))
  else
    None

let translate_signature cp_builder signature =
  CF.Attribute (CP.add_utf8 cp_builder "Signature", CF.Attr_Signature (CP.add_utf8 cp_builder signature))

let translate_field cp_builder attr_compiler f =
  let attrs = 
    (translate_generic_attrs cp_builder f.CD.fd_generic_attributes)
    @ (translate_custom_attrs cp_builder attr_compiler f.CD.fd_custom_attributes)
    +> (Option.map (translate_constant cp_builder) f.CD.fd_constant_value)
    +> (translate_visible_annotations cp_builder f.CD.fd_visible_annotations)
    +> (translate_invisible_annotations cp_builder f.CD.fd_invisible_annotations)
    +> (translate_deprecated cp_builder f.CD.fd_deprecated)
    +> (translate_synthetic cp_builder f.CD.fd_synthetic)
    +> (Option.map (translate_signature cp_builder) f.CD.fd_signature)
  in
    { CF.f_flags = f.CD.fd_flags
    ; CF.f_name  = CP.add_utf8 cp_builder f.CD.fd_name
    ; CF.f_desc  = CP.add_utf8 cp_builder (Jvmtype.string_of_type f.CD.fd_ty)
    ; CF.f_attrs = attrs
    }

let translate_visible_param_annotations cp_builder annotations = match annotations with
  | [] -> None
  | l ->
      Some (CF.Attribute (CP.add_utf8 cp_builder "RuntimeVisibleParameterAnnotations",
			  CF.Attr_RuntimeVisibleParameterAnnotations (List.map (List.map (translate_annotation cp_builder)) l)))

let translate_invisible_param_annotations cp_builder annotations = match annotations with
  | [] -> None
  | l ->
      Some (CF.Attribute (CP.add_utf8 cp_builder "RuntimeInvisibleParameterAnnotations",
			  CF.Attr_RuntimeInvisibleParameterAnnotations (List.map (List.map (translate_annotation cp_builder)) l)))

let translate_annotation_default cp_builder v =
  CF.Attribute (CP.add_utf8 cp_builder "AnnotationDefault",
		CF.Attr_AnnotationDefault (translate_element cp_builder v))

let translate_method cp_builder attr_compiler code_attr_compiler m =
  let _, return_ty = m.CD.md_sig in
  let attrs =
    (translate_generic_attrs cp_builder m.CD.md_generic_attributes)
    @ (translate_custom_attrs cp_builder attr_compiler m.CD.md_custom_attributes)
    +> (Option.map (translate_code cp_builder code_attr_compiler return_ty) m.CD.md_code)
    +> (translate_exceptions cp_builder m.CD.md_exceptions)
    +> (translate_visible_annotations cp_builder m.CD.md_visible_annotations)
    +> (translate_invisible_annotations cp_builder m.CD.md_invisible_annotations)
    +> (translate_visible_param_annotations cp_builder m.CD.md_visible_param_annotations)
    +> (translate_invisible_param_annotations cp_builder m.CD.md_invisible_param_annotations)
    +> (translate_deprecated cp_builder m.CD.md_deprecated)
    +> (translate_synthetic cp_builder m.CD.md_synthetic)
    +> (Option.map (translate_signature cp_builder) m.CD.md_signature)
    +> (Option.map (translate_annotation_default cp_builder) m.CD.md_annotation_default)
  in
    { CF.m_flags = m.CD.md_flags
    ; CF.m_name  = CP.add_utf8 cp_builder m.CD.md_name
    ; CF.m_desc  = CP.add_utf8 cp_builder (Jvmtype.string_of_methodsig m.CD.md_sig)
    ; CF.m_attrs = attrs
    }

let translate_innerclass_infos cp_builder classes = match classes with
  | [] -> None
  | classes ->
      let translate_innerclass_info i =
	{ CF.inner_info  = Option.map (fun x -> CP.add_class cp_builder (Jvmtype.TObject x)) i.CD.inner_info
	; CF.outer_info  = Option.map (fun x -> CP.add_class cp_builder (Jvmtype.TObject x)) i.CD.outer_info
	; CF.inner_name  = Option.map (CP.add_utf8 cp_builder) i.CD.inner_name
	; CF.inner_flags = i.CD.inner_flags
	}
      in
	Some (CF.Attribute (CP.add_utf8 cp_builder "InnerClasses",
			    CF.Attr_InnerClasses (List.map translate_innerclass_info classes)))
  
let translate_srcfile cp_builder srcfile =
  CF.Attribute (CP.add_utf8 cp_builder "SourceFile",
		CF.Attr_SourceFile (CP.add_utf8 cp_builder srcfile))

let compile decl attribute_compilers =
  let cp_builder = CP.create_builder () in
  let flags   = decl.CD.flags in
  let this    = CP.add_class cp_builder (Jvmtype.TObject decl.CD.this) in
  let super   = Option.map (fun x -> CP.add_class cp_builder (Jvmtype.TObject x)) decl.CD.super in
  let ifcs    = List.map (fun x -> CP.add_class cp_builder (Jvmtype.TObject x)) decl.CD.interfaces in
  let fields  = List.map (translate_field cp_builder attribute_compilers.compile_field_attribute) decl.CD.fields in
  let methods = List.map (translate_method cp_builder attribute_compilers.compile_method_attribute attribute_compilers.compile_code_attribute) decl.CD.methods in
  let attrs   =
    (translate_generic_attrs cp_builder decl.CD.generic_attributes)
    @ (translate_custom_attrs cp_builder attribute_compilers.compile_class_attribute decl.CD.custom_attributes)
    +> (translate_innerclass_infos cp_builder decl.CD.inner_classes)
    +> (translate_deprecated cp_builder decl.CD.deprecated)
    +> (Option.map (translate_srcfile cp_builder) decl.CD.srcfile)
    +> (translate_visible_annotations cp_builder decl.CD.visible_annotations)
    +> (translate_invisible_annotations cp_builder decl.CD.invisible_annotations)
    +> (translate_synthetic cp_builder decl.CD.synthetic)
    +> (Option.map (translate_enclosing_method cp_builder) decl.CD.enclosing_method)
    +> (Option.map (translate_signature cp_builder) decl.CD.signature)
    +> (Option.map (translate_source_debug_extension cp_builder) decl.CD.source_debug_extn)
  in
  let cp      = CP.pool_of_builder cp_builder in
    { CF.minor   = decl.CD.minor
    ; CF.major   = decl.CD.major
    ; CF.pool    = cp
    ; CF.flags   = flags
    ; CF.this    = this
    ; CF.super   = super
    ; CF.ifcs    = ifcs
    ; CF.fields  = fields
    ; CF.methods = methods
    ; CF.attrs   = attrs
    }

let to_file decl attribute_compilers file =
  ClassfileOutput.to_file (compile decl attribute_compilers) file

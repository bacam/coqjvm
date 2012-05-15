module CP = Constpool
module JT = Jvmtype
module CF = Classfile
module CD = Classdecl
module DB = DecompileBytecode

exception DecompileError of string

type ('f,'m,'c,'cl) attribute_decompilers =
    { empty_field_attribute      : 'f
    ; empty_method_attribute     : 'm
    ; empty_code_attribute       : 'c
    ; empty_class_attribute      : 'cl
    ; decompile_field_attribute  : 'f -> string * string -> Constpool.pool -> 'f option (** decompile field attributes *)
    ; decompile_method_attribute : 'm -> string * string -> Constpool.pool -> 'm option (** decompile method attributes *)
    ; decompile_code_attribute   : 'c -> string * string -> Constpool.pool -> (int -> Label.label) -> 'c option (** decompile code attributes *)
    ; decompile_class_attribute  : 'cl -> string * string -> Constpool.pool -> 'cl option (** decompile class attributes *)
    }

let null_attribute_decompilers =
  { empty_field_attribute      = ()
  ; empty_method_attribute     = ()
  ; empty_code_attribute       = ()
  ; empty_class_attribute      = ()
  ; decompile_field_attribute  = (fun l a _ -> None)
  ; decompile_method_attribute = (fun l a _ -> None)
  ; decompile_code_attribute   = (fun l a _ _ -> None)
  ; decompile_class_attribute  = (fun l a _ -> None)
  }

let decompile_exception_handler label_map_builder pool handler =
  { CD.exn_start = DB.decompile_offset label_map_builder handler.CF.exn_start
  ; CD.exn_end   = DB.decompile_offset label_map_builder handler.CF.exn_end
  ; CD.exn_entry = DB.decompile_offset label_map_builder handler.CF.exn_pc
  ; CD.exn_catch = Option.map (CP.lookup_class_notarray pool) handler.CF.exn_type
  }

let decompile_constantvalue pool idx =
  match CP.lookup pool idx with
    | CP.CPstring i -> CD.Cstring (CP.lookup_utf8 pool i)
    | CP.CPint i    -> CD.Cint i
    | CP.CPfloat f  -> CD.Cfloat f
    | CP.CPlong l   -> CD.Clong l
    | CP.CPdouble d -> CD.Cdouble d
    | CP.CPutf8 _   -> raise (DecompileError "Invalid constant value: utf8")
    | _             -> raise (DecompileError "Invalid constant value")

let decompile_inner_class_info pool inner_class_info =
  { CD.inner_info = Option.map (CP.lookup_class_notarray pool) inner_class_info.CF.inner_info
  ; CD.outer_info = Option.map (CP.lookup_class_notarray pool) inner_class_info.CF.outer_info
  ; CD.inner_name = Option.map (CP.lookup_utf8 pool) inner_class_info.CF.inner_name
  ; CD.inner_flags = inner_class_info.CF.inner_flags
  }

let decompile_line_number_info label_map_builder line_number_info =
  { CD.ln_start = DB.decompile_offset label_map_builder line_number_info.CF.ln_start
  ; CD.ln_line  = line_number_info.CF.ln_line
  }

let decompile_localvar_info label_map_builder pool localvar_info =
  { CD.lv_from  = DB.decompile_offset label_map_builder localvar_info.CF.lv_start
  ; CD.lv_thru  = DB.decompile_offset label_map_builder (localvar_info.CF.lv_start + localvar_info.CF.lv_length)
  ; CD.lv_name  = CP.lookup_utf8 pool localvar_info.CF.lv_name
  ; CD.lv_ty    = CP.lookup_type pool localvar_info.CF.lv_desc
  ; CD.lv_index = localvar_info.CF.lv_index
  }

let decompile_localvartype_info label_map_builder pool localvartype_info =
  { CD.vt_from  = DB.decompile_offset label_map_builder localvartype_info.CF.vt_start
  ; CD.vt_thru  = DB.decompile_offset label_map_builder (localvartype_info.CF.vt_start + localvartype_info.CF.vt_length)
  ; CD.vt_name  = CP.lookup_utf8 pool localvartype_info.CF.vt_name
  ; CD.vt_sign  = CP.lookup_utf8 pool localvartype_info.CF.vt_sign
  ; CD.vt_index = localvartype_info.CF.vt_index
  }

let rec decompile_element pool element = match element with (* FIXME: do overflow checks? *)
  | CF.Const_Value (CF.String, idx)  -> CD.Const_string (CP.lookup_utf8 pool idx)
  | CF.Const_Value (CF.Byte, idx)    -> CD.Const_byte (Int32.to_int (CP.lookup_int pool idx))
  | CF.Const_Value (CF.Char, idx)    -> CD.Const_char (CP.lookup_int pool idx)
  | CF.Const_Value (CF.Double, idx)  -> CD.Const_double (CP.lookup_double pool idx)
  | CF.Const_Value (CF.Float, idx)   -> CD.Const_float (CP.lookup_float pool idx)
  | CF.Const_Value (CF.Int, idx)     -> CD.Const_int (CP.lookup_int pool idx)
  | CF.Const_Value (CF.Long, idx)    -> CD.Const_long (CP.lookup_long pool idx)
  | CF.Const_Value (CF.Short, idx)   -> CD.Const_short (Int32.to_int (CP.lookup_int pool idx))
  | CF.Const_Value (CF.Bool, idx)    -> CD.Const_bool (Int32.to_int (CP.lookup_int pool idx))
  | CF.Enum_Const_Value (idx1, idx2) ->
      let enum_type_str = CP.lookup_utf8 pool idx1 in
      let enum_type = match Jvmtype.class_of_string enum_type_str with
	| None -> raise (DecompileError (Printf.sprintf "Invalid type in annotation: %s" enum_type_str))
	| Some jtype -> jtype
      in
	CD.Enum_Const_Value (enum_type, CP.lookup_utf8 pool idx2)
  | CF.Class_Info idx                -> CD.Class_Info (CP.lookup_utf8 pool idx)
  | CF.Annot_Value annot             -> CD.Annot_Value (decompile_annotation pool annot)
  | CF.Array_Value elements          -> CD.Array_Value (List.map (decompile_element pool) elements)
	
and decompile_element_pair pool (name_idx, element) =
  (CP.lookup_utf8 pool name_idx, decompile_element pool element)

and decompile_annotation pool (type_idx, elements) =
  let annot_type_str = CP.lookup_utf8 pool type_idx in
  let annot_type = match Jvmtype.type_of_string annot_type_str with
    | None -> raise (DecompileError (Printf.sprintf "Invalid type in annotation: %s" annot_type_str))
    | Some jtype -> jtype
  in
  let elements = List.map (decompile_element_pair pool) elements in
    (annot_type, elements)

let decompile_vtype_info label_map_builder pool vtype = match vtype with
  | CF.Top_vi                  -> CD.Top_vi
  | CF.Integer_vi              -> CD.Integer_vi
  | CF.Float_vi                -> CD.Float_vi
  | CF.Long_vi                 -> CD.Long_vi
  | CF.Double_vi               -> CD.Double_vi
  | CF.Null_vi                 -> CD.Null_vi
  | CF.UninitializedThis_vi    -> CD.UninitializedThis_vi
  | CF.Object_vi idx           -> CD.Object_vi (CP.lookup_class pool idx)
  | CF.Uninitialized_vi offset -> CD.Uninitialized_vi (DB.decompile_offset label_map_builder offset)

let decompile_stackmap label_map_builder pool frames =
  let rec process_frames offset frames decompiled_frames = match frames with
    | [] ->
	List.rev decompiled_frames
    | (delta, frame)::frames ->
	let offset = offset + delta in
	let label  = DB.decompile_offset label_map_builder offset in
	let frame  = match frame with
	  | CF.Same_frame              -> CD.Same_frame
	  | CF.Same_locals_1_stk vtype -> CD.Same_locals_1_stk (decompile_vtype_info label_map_builder pool vtype)
	  | CF.Chop_frame i            -> CD.Chop_frame i
	  | CF.Append_frame l          -> CD.Append_frame (List.map (decompile_vtype_info label_map_builder pool) l)
	  | CF.Full_frame (l,s)        -> CD.Full_frame (List.map (decompile_vtype_info label_map_builder pool) l,
							 List.map (decompile_vtype_info label_map_builder pool) s)
	in
	  process_frames offset frames ((label,frame)::decompiled_frames)
  in
    process_frames 0 frames []

let decompile_cldc_stackmap label_map_builder pool (offset, CF.CLDC_full_frame (stack, locals)) = (* FIXME: is this the right way round? use a record *)
  let label  = DB.decompile_offset label_map_builder offset in
  let stack  = List.map (decompile_vtype_info label_map_builder pool) stack in
  let locals = List.map (decompile_vtype_info label_map_builder pool) locals in
    (label, stack, locals)

let decompile_code_attribute label_map_builder pool attr_decompiler cdecl (CF.Attribute (name_idx,attr)) =
  let name = CP.lookup_utf8 pool name_idx in
    match attr with
      | CF.Attr_LineNumberTable table -> {cdecl with CD.code_line_numbers = Some (List.map (decompile_line_number_info label_map_builder) table)}
      | CF.Attr_LocalVariableTable table -> {cdecl with CD.code_localvars = Some (List.map (decompile_localvar_info label_map_builder pool) table)}
      | CF.Attr_LocalVariableTypeTable table -> {cdecl with CD.code_localvartypes = Some (List.map (decompile_localvartype_info label_map_builder pool) table)}
      | CF.Attr_StackMapTable stackmaptable -> {cdecl with CD.code_stackmap = Some (decompile_stackmap label_map_builder pool stackmaptable)}
      | CF.Attr_StackMap stackmap -> {cdecl with CD.code_cldc_stackmap = Some (List.map (decompile_cldc_stackmap label_map_builder pool) stackmap)}
      | CF.Attr data -> 
	  (match attr_decompiler cdecl.CD.code_custom_attributes (name,data) pool (DB.decompile_offset label_map_builder) with
	     | None   -> {cdecl with CD.code_generic_attributes = (name,data)::cdecl.CD.code_generic_attributes}
	     | Some a -> {cdecl with CD.code_custom_attributes  = a})
      | _ -> raise (DecompileError (Printf.sprintf "Attribute '%s' not allowed in code" name))

let decompile_code pool attr_decompilers (max_stack, max_locals, instrs, handlers, attrs) =
  let label_map_builder = DB.create_label_map_builder () in
  let handlers = List.map (decompile_exception_handler label_map_builder pool) handlers in
  let code_decl =
    { CD.code_max_stack  = max_stack
    ; CD.code_locals     = max_locals
    ; CD.code_code       = []
    ; CD.code_handlers   = handlers
    ; CD.code_line_numbers     = None
    ; CD.code_localvars        = None
    ; CD.code_localvartypes    = None
    ; CD.code_stackmap         = None
    ; CD.code_cldc_stackmap    = None
    ; CD.code_custom_attributes = attr_decompilers.empty_code_attribute
    ; CD.code_generic_attributes = []
    }
  in
  let code_decl = List.fold_left (decompile_code_attribute label_map_builder pool attr_decompilers.decompile_code_attribute) code_decl attrs in
  let instrs    = DB.decompile_bytecode pool label_map_builder instrs in
    {code_decl with CD.code_code = instrs}

let decompile_enclosing_method pool (class_idx, method_idx) =
  { CD.ec_class  = CP.lookup_class_notarray pool class_idx
  ; CD.ec_method = Option.map (CP.lookup_methoddesc pool) method_idx
  }

let decompile_field_attribute pool attr_decompiler fdecl (CF.Attribute (name_idx, attr)) =
  let name = CP.lookup_utf8 pool name_idx in
    match attr with (* FIXME: complain if we repeat an attribute *)
      | CF.Attr_ConstantValue value -> {fdecl with CD.fd_constant_value = Some (decompile_constantvalue pool value) }
      | CF.Attr_Deprecated          -> {fdecl with CD.fd_deprecated = true}
      | CF.Attr_Synthetic           -> {fdecl with CD.fd_synthetic = true}
      | CF.Attr_Signature idx       -> {fdecl with CD.fd_signature = Some (CP.lookup_utf8 pool idx)}
      | CF.Attr_RuntimeVisibleAnnotations annotations
                                    -> {fdecl with CD.fd_visible_annotations = List.map (decompile_annotation pool) annotations}
      | CF.Attr_RuntimeInvisibleAnnotations annotations
                                    -> {fdecl with CD.fd_invisible_annotations = List.map (decompile_annotation pool) annotations}
      | CF.Attr data                -> 
	  (match attr_decompiler fdecl.CD.fd_custom_attributes (name,data) pool with
	     | None   -> {fdecl with CD.fd_generic_attributes = (name,data)::fdecl.CD.fd_generic_attributes}
	     | Some a -> {fdecl with CD.fd_custom_attributes  = a})
      | _ -> raise (DecompileError (Printf.sprintf "Attribute %s not allowed in a field" name))

let decompile_field pool attr_decompilers field_decl =
  let fdecl =
    { CD.fd_flags			= field_decl.CF.f_flags
    ; CD.fd_name			= CP.lookup_utf8 pool field_decl.CF.f_name
    ; CD.fd_ty				= CP.lookup_type pool field_decl.CF.f_desc
    ; CD.fd_generic_attributes		= []
    ; CD.fd_custom_attributes		= attr_decompilers.empty_field_attribute
    ; CD.fd_constant_value		= None
    ; CD.fd_visible_annotations		= []
    ; CD.fd_invisible_annotations	= []
    ; CD.fd_deprecated			= false
    ; CD.fd_synthetic			= false
    ; CD.fd_signature			= None
    }
  in
    List.fold_left (decompile_field_attribute pool attr_decompilers.decompile_field_attribute) fdecl field_decl.CF.f_attrs

let decompile_method_attribute pool attr_decompilers mdecl (CF.Attribute (name_idx, attr)) =
  let name = CP.lookup_utf8 pool name_idx in
    match attr with
      | CF.Attr_Code (max_stack, max_locals, instrs, handlers, attrs)
	                        -> {mdecl with CD.md_code = Some (decompile_code pool attr_decompilers (max_stack, max_locals, instrs, handlers, attrs))}
      | CF.Attr_Exceptions exns -> {mdecl with CD.md_exceptions = List.map (CP.lookup_class_notarray pool) exns}
      | CF.Attr_RuntimeVisibleAnnotations annotations
                                -> {mdecl with CD.md_visible_annotations = List.map (decompile_annotation pool) annotations}
      | CF.Attr_RuntimeInvisibleAnnotations annotations
                                -> {mdecl with CD.md_invisible_annotations = List.map (decompile_annotation pool) annotations}
      | CF.Attr_RuntimeVisibleParameterAnnotations annotations
                                -> {mdecl with CD.md_visible_param_annotations = List.map (List.map (decompile_annotation pool)) annotations}
      | CF.Attr_RuntimeInvisibleParameterAnnotations annotations
                                -> {mdecl with CD.md_invisible_param_annotations = List.map (List.map (decompile_annotation pool)) annotations}
      | CF.Attr_Deprecated      -> {mdecl with CD.md_deprecated = true}
      | CF.Attr_Synthetic       -> {mdecl with CD.md_synthetic = true}
      | CF.Attr data            -> 
	  (match attr_decompilers.decompile_method_attribute mdecl.CD.md_custom_attributes (name,data) pool with
	     | None   -> {mdecl with CD.md_generic_attributes = (name,data)::mdecl.CD.md_generic_attributes}
	     | Some a -> {mdecl with CD.md_custom_attributes  = a})
      | CF.Attr_Signature idx   -> {mdecl with CD.md_signature = Some (CP.lookup_utf8 pool idx)}
      | CF.Attr_AnnotationDefault el -> {mdecl with CD.md_annotation_default = Some (decompile_element pool el)}
      | _ -> raise (DecompileError (Printf.sprintf "Attribute '%s' not allowed in methods" name))

let decompile_method pool attr_decompilers method_decl =
  let mdecl = 
    { CD.md_flags   = method_decl.CF.m_flags
    ; CD.md_name    = CP.lookup_utf8 pool method_decl.CF.m_name
    ; CD.md_sig     = CP.lookup_methodsig pool method_decl.CF.m_desc
    ; CD.md_generic_attributes = []
    ; CD.md_custom_attributes = attr_decompilers.empty_method_attribute
    ; CD.md_code             = None
    ; CD.md_exceptions       = []
    ; CD.md_visible_annotations = []
    ; CD.md_invisible_annotations = []
    ; CD.md_visible_param_annotations = []
    ; CD.md_invisible_param_annotations = []
    ; CD.md_deprecated = false
    ; CD.md_synthetic = false
    ; CD.md_signature = None
    ; CD.md_annotation_default = None
    }
  in
  let md = List.fold_left (decompile_method_attribute pool attr_decompilers) mdecl method_decl.CF.m_attrs in
    {md with CD.md_generic_attributes = List.rev md.CD.md_generic_attributes}

type 'a class_attributes =
    { ca_srcfile               : string option
    ; ca_deprecated            : bool
    ; ca_synthetic             : bool
    ; ca_visible_annotations   : CD.annotation list
    ; ca_invisible_annotations : CD.annotation list
    ; ca_inner_classes         : CD.inner_class_info list
    ; ca_custom               : 'a
    ; ca_generic               : (string * string) list
    ; ca_enclosing_method      : CD.enclosing_method_info option
    ; ca_signature             : string option
    ; ca_source_debug_extn     : string option
    }

let empty_class_attributes empty_attrs =
  { ca_srcfile    = None
  ; ca_deprecated = false
  ; ca_synthetic = false
  ; ca_visible_annotations = []
  ; ca_invisible_annotations = []
  ; ca_inner_classes = []
  ; ca_generic = []
  ; ca_custom = empty_attrs
  ; ca_enclosing_method = None
  ; ca_signature = None
  ; ca_source_debug_extn = None
  }

let decompile_class_attribute pool attr_decompiler ca (CF.Attribute (name_idx, attr)) =
  let name = CP.lookup_utf8 pool name_idx in
    match attr with
      | CF.Attr_InnerClasses l         -> {ca with ca_inner_classes=List.map (decompile_inner_class_info pool) l}
      | CF.Attr_Synthetic              -> {ca with ca_synthetic=true}
      | CF.Attr_Signature idx          -> {ca with ca_signature=Some (CP.lookup_utf8 pool idx)}
      | CF.Attr_SourceFile idx         -> {ca with ca_srcfile=Some (CP.lookup_utf8 pool idx)}
      | CF.Attr_SourceDebugExtension s -> {ca with ca_source_debug_extn = Some s}
      | CF.Attr_Deprecated             -> {ca with ca_deprecated=true}
      | CF.Attr_RuntimeVisibleAnnotations l   -> {ca with ca_visible_annotations=List.map (decompile_annotation pool) l}
      | CF.Attr_RuntimeInvisibleAnnotations l -> {ca with ca_invisible_annotations=List.map (decompile_annotation pool) l}
      | CF.Attr_EnclosingMethod (class_idx,method_idx) -> {ca with ca_enclosing_method=Some (decompile_enclosing_method pool (class_idx, method_idx))}
      | CF.Attr data                   -> 
	  (match attr_decompiler ca.ca_custom (name,data) pool with
	     | None   -> {ca with ca_generic = (name,data)::ca.ca_generic}
	     | Some a -> {ca with ca_custom  = a})
      | _ -> raise (DecompileError (Printf.sprintf "Attribute '%s' not allowed in class's attributes" name))

let decompile cf attribute_decompilers =
  let pool = cf.CF.pool in
  let ca   = List.fold_left (decompile_class_attribute pool attribute_decompilers.decompile_class_attribute) (empty_class_attributes attribute_decompilers.empty_class_attribute) cf.CF.attrs in
    { CD.major       = cf.CF.major
    ; CD.minor       = cf.CF.minor
    ; CD.flags       = cf.CF.flags
    ; CD.this        = CP.lookup_class_notarray pool cf.CF.this
    ; CD.super       = Option.map (CP.lookup_class_notarray pool) cf.CF.super
    ; CD.interfaces  = List.map (CP.lookup_class_notarray pool) cf.CF.ifcs
    ; CD.fields      = List.map (decompile_field pool attribute_decompilers) cf.CF.fields
    ; CD.methods     = List.map (decompile_method pool attribute_decompilers) cf.CF.methods

    ; CD.srcfile               = ca.ca_srcfile
    ; CD.deprecated            = ca.ca_deprecated
    ; CD.visible_annotations   = ca.ca_visible_annotations
    ; CD.invisible_annotations = ca.ca_invisible_annotations
    ; CD.inner_classes         = ca.ca_inner_classes
    ; CD.generic_attributes    = List.rev ca.ca_generic
    ; CD.custom_attributes     = ca.ca_custom
    ; CD.synthetic             = ca.ca_synthetic
    ; CD.enclosing_method      = ca.ca_enclosing_method
    ; CD.signature             = ca.ca_signature
    ; CD.source_debug_extn     = ca.ca_source_debug_extn
    }

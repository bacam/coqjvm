(* Classdecl.sml
 *
 * K. MacKenzie
 * May 2006
 *)

type constant =
  | Cint    of int32
  | Cfloat  of JFloat.t
  | Clong   of int64
  | Cdouble of float
  | Cstring of string

(*--- Java 5 annotations ---*)

type element = (* FIXME: are these the best representations? *)
  | Const_byte       of int
  | Const_char       of int32
  | Const_double     of float
  | Const_float      of JFloat.t
  | Const_int        of int32
  | Const_long       of int64
  | Const_short      of int
  | Const_bool       of int
  | Const_string     of string
  | Enum_Const_Value of Jvmtype.jclass * string  (* e *)
  | Class_Info       of string           (* c *)
  | Annot_Value      of annotation       (* @ *)
  | Array_Value      of element list     (* [ *)

and annotation = Jvmtype.jtype * (string * element) list

(*--- end ---*)

type exn_hdl =                       (* exception handler declaration *)
    { exn_start: Label.label		(* start of handler scope *)
    ; exn_end:   Label.label		(* end of handler scope *)
    ; exn_entry: Label.label		(* handler entry point *)
    ; exn_catch: Jvmtype.jclass option	        (* class of handled exception; None = any *)
    }

type vtype_info =  (* verification_type_info: jvm spec, 4.8.4 *)
    Top_vi
  | Integer_vi
  | Float_vi
  | Long_vi
  | Double_vi
  | Null_vi
  | UninitializedThis_vi
  | Object_vi of Jvmtype.jref_type
  | Uninitialized_vi of Label.label (* Location of corresponding 'new' opcode *)

type stackmap_frame =
    Same_frame                                            (* same as previous frame *)
  | Same_locals_1_stk of vtype_info                    (* one stack item *)
  | Chop_frame of int                                     (* some locals deleted *)
  | Append_frame of vtype_info list                    (* extra locals *)
  | Full_frame of vtype_info list * vtype_info list (* all locals, all stack *)

type stackmap_info = Label.label * stackmap_frame

type cldc_stackmap_info = Label.label * vtype_info list * vtype_info list   (* all locals, all stack *)

(* Note: same_frame_extended and same_locals_1_stack_item_frame_extended are
   omitted:  they're generated during code emission if necessary *)

type inner_class_info =
    { inner_info: Jvmtype.jclass option
    ; outer_info: Jvmtype.jclass option
    ; inner_name: string option
    ; inner_flags: AccessFlags.class_flags
    }

type line_number_info =
    { ln_start: Label.label
    ; ln_line:  int
    }

type localvar_info =
    { lv_from:  Label.label
    ; lv_thru:  Label.label
    ; lv_name:  string
    ; lv_ty:    Jvmtype.jtype
    ; lv_index: int
    }

type localvartype_info =
    { vt_from:  Label.label
    ; vt_thru:  Label.label
    ; vt_name:  string
    ; vt_sign:  string
    ; vt_index: int
    }

type enclosing_method_info =
    { ec_class:  Jvmtype.jclass
    ; ec_method: (string * Jvmtype.methodsig) option
    }

type 'c code_info =
    { code_max_stack        : int		     (* max operand stack depth *)
    ; code_locals           : int		     (* max size of local vars *)
    ; code_code             : unit Bytecode.instr list (* instruction sequence *)
    ; code_handlers         : exn_hdl list	     (* exception handlers *)
    ; code_line_numbers     : line_number_info list option
    ; code_localvars        : localvar_info list option
    ; code_localvartypes    : localvartype_info list option
    ; code_stackmap         : stackmap_info list option
    ; code_cldc_stackmap    : cldc_stackmap_info list option
    ; code_custom_attributes : 'c
    ; code_generic_attributes : (string * string) list
    }

let code ~max_stack ~locals ~code ~custom_attributes ?(handlers=[]) ?line_numbers ?localvars ?localvartypes ?stackmap ?cldc_stackmap ?(generic_attributes=[]) () =
  { code_max_stack = max_stack
  ; code_locals    = locals
  ; code_code      = code
  ; code_handlers  = handlers
  ; code_line_numbers = line_numbers
  ; code_localvars    = localvars
  ; code_localvartypes = localvartypes
  ; code_stackmap      = stackmap
  ; code_cldc_stackmap = cldc_stackmap
  ; code_custom_attributes = custom_attributes
  ; code_generic_attributes = generic_attributes
  }

(* Fields, methods and classes *)


type 'f field_decl =	                  (* field declaration *)
   { fd_flags:  AccessFlags.field_flags	  (* access flags *)
   ; fd_name:   string		          (* unqualified name *)
   ; fd_ty:     Jvmtype.jtype		  (* field type *)
   ; fd_custom_attributes    : 'f
   ; fd_constant_value      : constant option
   ; fd_visible_annotations : annotation list
   ; fd_invisible_annotations : annotation list
   ; fd_deprecated            : bool
   ; fd_synthetic             : bool
   ; fd_signature             : string option
   ; fd_generic_attributes    : (string * string) list
   }

let field_decl ~flags ~name ~ty
    ~custom_attributes ?(generic_attributes=[]) ?(constant_value=None)
    ?(visible_annotations=[]) ?(invisible_annotations=[])
    ?(deprecated=false) ?(synthetic=false)
    ?(signature=None) () =
  { fd_flags = flags
  ; fd_name  = name
  ; fd_ty    = ty
  ; fd_custom_attributes = custom_attributes
  ; fd_generic_attributes = generic_attributes
  ; fd_constant_value = constant_value
  ; fd_visible_annotations = visible_annotations
  ; fd_invisible_annotations = invisible_annotations
  ; fd_deprecated = deprecated
  ; fd_synthetic = synthetic
  ; fd_signature = signature
  }

type ('m,'c) method_decl =	                  (* method declaration *)
   { md_flags : AccessFlags.method_flags  (* access flags *)
   ; md_name  : string		          (* unqualified name *)
   ; md_sig   : Jvmtype.methodsig	  (* method signature *)
   ; md_custom_attributes  : 'm
   ; md_generic_attributes : (string * string) list
   ; md_code  : 'c code_info option
   ; md_exceptions : Jvmtype.jclass list
   ; md_visible_annotations : annotation list
   ; md_invisible_annotations : annotation list
   ; md_visible_param_annotations : annotation list list
   ; md_invisible_param_annotations : annotation list list
   ; md_deprecated                  : bool
   ; md_synthetic                   : bool
   ; md_signature                   : string option
   ; md_annotation_default          : element option
   }

let method_decl ~flags ~name ~msig ?code ~custom_attributes
    ?(generic_attributes=[])
    ?(exceptions=[])
    ?(visible_annotations=[]) ?(invisible_annotations=[])
    ?(visible_param_annotations=[]) ?(invisible_param_annotations=[])
    ?(deprecated=false) ?(synthetic=false)
    ?(signature=None) ?(annotation_default=None) () =
  { md_flags               = flags
  ; md_name                = name
  ; md_sig                 = msig
  ; md_custom_attributes    = custom_attributes
  ; md_generic_attributes   = generic_attributes
  ; md_code                = code
  ; md_exceptions          = exceptions
  ; md_visible_annotations = visible_annotations
  ; md_invisible_annotations = invisible_annotations
  ; md_visible_param_annotations = visible_param_annotations
  ; md_invisible_param_annotations = invisible_param_annotations
  ; md_deprecated = deprecated
  ; md_synthetic  = synthetic
  ; md_signature  = signature
  ; md_annotation_default = annotation_default
  }

type ('f,'m,'c,'cl) class_decl =
    { major                 : int
    ; minor                 : int
    ; flags                 : AccessFlags.class_flags
    ; this                  : Jvmtype.jclass
    ; super                 : Jvmtype.jclass option
    ; interfaces            : Jvmtype.jclass list
    ; fields                : 'f field_decl list
    ; methods               : ('m, 'c) method_decl list
    ; srcfile               : string option
    ; deprecated            : bool
    ; visible_annotations   : annotation list
    ; invisible_annotations : annotation list
    ; inner_classes         : inner_class_info list
    ; custom_attributes      : 'cl
    ; generic_attributes     : (string * string) list
    ; synthetic             : bool
    ; enclosing_method      : enclosing_method_info option
    ; signature             : string option
    ; source_debug_extn     : string option
    }

let class_decl ?(major=45) ?(minor=3) ~flags ~this ~super ~custom_attributes ?(generic_attributes=[]) ?(interfaces=[])
 ~fields ~methods ?srcfile ?(deprecated=false)
 ?(visible_annotations=[]) ?(invisible_annotations=[]) ?(inner_classes=[])
 ?(synthetic=false) ?(enclosing_method=None)
 ?(signature=None) ?(source_debug_extn=None) () =
  { major = major
  ; minor = minor
  ; flags = flags
  ; this  = this
  ; super = super
  ; interfaces = interfaces
  ; fields     = fields
  ; methods    = methods
  ; srcfile    = srcfile
  ; deprecated = deprecated
  ; visible_annotations = visible_annotations
  ; invisible_annotations = invisible_annotations
  ; inner_classes = inner_classes
  ; custom_attributes = custom_attributes
  ; generic_attributes = generic_attributes
  ; synthetic = synthetic
  ; enclosing_method = enclosing_method
  ; signature = signature
  ; source_debug_extn = source_debug_extn
  }

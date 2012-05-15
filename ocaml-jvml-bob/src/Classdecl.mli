(** High-level representation of Java [.class] files

    @author Kenneth MacKenzie
*)

(**{1 High-level Class file Representation}

   This module contains the type definitions for a high-level
   representation of Java [.class] files. This representation is
   intended to be close an assembler-like format for [.class] files,
   and to be easy for a compiler to produce. *)

(**{2 Constant values for fields} *)

(** Constant values for fields *)
type constant =
  | Cint    of int32
  | Cfloat  of JFloat.t
  | Clong   of int64
  | Cdouble of float
  | Cstring of string

(**{2 Inner class information} *)

(** Inner class information *)
type inner_class_info =
    { inner_info:  Jvmtype.jclass option
    ; outer_info:  Jvmtype.jclass option
    ; inner_name:  string option
    ; inner_flags: AccessFlags.class_flags
    }

(**{2 Line number information} *)

(** Line number information *)
type line_number_info =
    { ln_start: Label.label
    ; ln_line:  int
    }

(**{2 Local variable information} *)

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

(**{2 Enclosing method information} *)

type enclosing_method_info =
    { ec_class:  Jvmtype.jclass
    ; ec_method: (string * Jvmtype.methodsig) option
    }

(**{2 Annotations} *)

(** Annotation elements *)
type element =
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

(** Annotations *)
and annotation = Jvmtype.jtype * (string * element) list

(**{2 Exception Handlers} *)

(** Exception handler declarations *)
type exn_hdl =
    { exn_start: Label.label		(** start of handler scope *)
    ; exn_end:   Label.label		(** end of handler scope *)
    ; exn_entry: Label.label		(** handler entry point *)
    ; exn_catch: Jvmtype.jclass option	(** class of handled exception; [None] = any *)
    }

(**{2 Stack maps}
   Note: same_frame_extended and same_locals_1_stack_item_frame_extended are
   omitted:  they're generated during code emission if necessary *)

(** Verification types *)
type vtype_info =
    Top_vi
  | Integer_vi
  | Float_vi
  | Long_vi
  | Double_vi
  | Null_vi
  | UninitializedThis_vi
  | Object_vi of Jvmtype.jref_type
  | Uninitialized_vi of Label.label (** The label gives the location of corresponding 'new' opcode *)

(** Stack map frames *)
type stackmap_frame =
    Same_frame                                            (** same as previous frame *)
  | Same_locals_1_stk of vtype_info                    (** one stack item *)
  | Chop_frame of int                                     (** some locals deleted *)
  | Append_frame of vtype_info list                    (** extra locals *)
  | Full_frame of vtype_info list * vtype_info list (** all locals, all stack *)
      
(** A stack map with a label in the code *)
type stackmap_info = Label.label * stackmap_frame

(** A CLDC-style stackmap *)
type cldc_stackmap_info = Label.label * vtype_info list * vtype_info list

(**{2 Code} *)

type 'c code_info =
    { code_max_stack          : int		     (* max operand stack depth *)
    ; code_locals             : int		     (* max size of local vars *)
    ; code_code               : unit Bytecode.instr list (* instruction sequence *)
    ; code_handlers           : exn_hdl list	     (* exception handlers *)
    ; code_line_numbers       : line_number_info list option
    ; code_localvars          : localvar_info list option
    ; code_localvartypes      : localvartype_info list option
    ; code_stackmap           : stackmap_info list option
    ; code_cldc_stackmap      : cldc_stackmap_info list option
    ; code_custom_attributes  : 'c
    ; code_generic_attributes : (string * string) list
    }

val code : max_stack:int ->
  locals:int -> 
  code:unit Bytecode.instr list ->
  custom_attributes:'c ->
  ?handlers:exn_hdl list ->
  ?line_numbers:line_number_info list ->
  ?localvars:localvar_info list ->
  ?localvartypes:localvartype_info list ->
  ?stackmap:stackmap_info list ->
  ?cldc_stackmap:cldc_stackmap_info list ->
  ?generic_attributes:(string * string) list ->
  unit ->
  'c code_info

(**{2 Fields, methods and classes} *)

(** High-level field declaration *)
type 'f field_decl =
   { fd_flags         : AccessFlags.field_flags	  (** access flags *)
   ; fd_name          : string		          (** unqualified name *)
   ; fd_ty            : Jvmtype.jtype		  (** field type *)
   ; fd_custom_attributes : 'f            (** field attributes *)
   ; fd_constant_value : constant option (** default value *)
   ; fd_visible_annotations : annotation list (** runtime visible annotations *)
   ; fd_invisible_annotations : annotation list (** runtime invisible annotations *)
   ; fd_deprecated       : bool (** deprecated flag *)
   ; fd_synthetic        : bool (** synthetic flags *)
   ; fd_signature        : string option (** signature *)
   ; fd_generic_attributes : (string * string) list
   }

val field_decl :
  flags:AccessFlags.field_flags ->
  name:string ->
  ty:Jvmtype.jtype ->
  custom_attributes:'f ->
  ?generic_attributes:(string * string) list ->
  ?constant_value:constant option ->
  ?visible_annotations:annotation list ->
  ?invisible_annotations:annotation list ->
  ?deprecated:bool ->
  ?synthetic:bool -> ?signature:string option -> unit -> 'f field_decl

(** High-level method declaration *)
type ('m, 'c) method_decl =
   { md_flags          : AccessFlags.method_flags (** access flags *)
   ; md_name           : string		          (** unqualified name *)
   ; md_sig            : Jvmtype.methodsig	  (** method signature *)

   ; md_custom_attributes  : 'm   (** method attributes *)
   ; md_generic_attributes : (string * string) list
   ; md_code           : 'c code_info option         (** method's code *)
   ; md_exceptions     : Jvmtype.jclass list      (** throws clause *)
   ; md_visible_annotations : annotation list     (** runtime visible annotations *)
   ; md_invisible_annotations : annotation list   (** runtime invisible annotations *)
   ; md_visible_param_annotations : annotation list list (** runtime visible parameter annotations *)
   ; md_invisible_param_annotations : annotation list list (** runtime invisible parameter annotations *)
   ; md_deprecated       : bool (** deprecated flag *)
   ; md_synthetic        : bool (** synthetic flags *)
   ; md_signature        : string option (** signature *)
   ; md_annotation_default : element option
   }

val method_decl :
  flags:AccessFlags.method_flags ->
  name:string ->
  msig:Jvmtype.methodsig ->
  ?code:'c code_info ->
  custom_attributes:'m ->
  ?generic_attributes:(string * string) list ->
  ?exceptions:Jvmtype.jclass list ->
  ?visible_annotations:annotation list ->
  ?invisible_annotations:annotation list ->
  ?visible_param_annotations:annotation list list ->
  ?invisible_param_annotations:annotation list list ->
  ?deprecated:bool ->
  ?synthetic:bool ->
  ?signature:string option ->
  ?annotation_default:element option -> unit -> ('m, 'c) method_decl

(** High-level class declaration *)
type ('f,'m,'c,'cl) class_decl =
    { major:       int (** major version number *)
    ; minor:       int              (** minor version number *)
    ; flags:       AccessFlags.class_flags (** access flags *)
    ; this:        Jvmtype.jclass	          (** the name of this class or interface *)
    ; super:       Jvmtype.jclass option	  (** the name of the super class (if any) *)
    ; interfaces:  Jvmtype.jclass list		  (** names of directly implemented interfaces *)
    ; fields:      'f field_decl list	  (** field declarations *)
    ; methods:     ('m, 'c) method_decl list	  (** method declarations *)

    ; srcfile               : string option (** the source file (optional) *)
    ; deprecated            : bool (** deprecated flag *)
    ; visible_annotations   : annotation list (** runtime visible annotations *)
    ; invisible_annotations : annotation list (** runtime invisible annotations *)
    ; inner_classes         : inner_class_info list (** inner class information *)
    ; custom_attributes      : 'cl (** custom attributes *)
    ; generic_attributes     : (string * string) list
    ; synthetic             : bool (** synthetic flag *)
    ; enclosing_method      : enclosing_method_info option (** enclosing method *)
    ; signature             : string option (** signature *)
    ; source_debug_extn     : string option (** source debug extension *)
    }

val class_decl :
  ?major:int ->
  ?minor:int ->
  flags:AccessFlags.class_flags ->
  this:Jvmtype.jclass ->
  super:Jvmtype.jclass option ->
  custom_attributes:'cl ->
  ?generic_attributes:(string * string) list ->
  ?interfaces:Jvmtype.jclass list ->
  fields:'f field_decl list ->
  methods:('m,'c) method_decl list ->
  ?srcfile:string ->
  ?deprecated:bool ->
  ?visible_annotations:annotation list ->
  ?invisible_annotations:annotation list ->
  ?inner_classes:inner_class_info list ->
  ?synthetic:bool ->
  ?enclosing_method:enclosing_method_info option ->
  ?signature:string option ->
  ?source_debug_extn:string option -> unit -> ('f,'m,'c,'cl) class_decl

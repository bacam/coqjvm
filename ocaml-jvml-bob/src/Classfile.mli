(** In-memory representation of Java [.class] files. *)

(**{1 Class file Representation} 

   This module contains the type definitions for representing Java
   [.class] files in memory.
*)


(** Type alias to indicate that the value should be an unsigned 16bit
    integer. *)
type u2 = int

(**{2 Exception handlers} *)

(** Records representing exception handlers. These are attached to
    [Code] attributes; see the {!Classfile.attribute} type below. *)
type exn_hdl =
    { exn_start : u2 (** offset in the bytecode *)
    ; exn_end   : u2 (** offset in the bytecode *)
    ; exn_pc    : u2 (** offset in the bytecode *)
    ; exn_type  : Constpool.index option (** index of the catch type, or None for any type *)
    }

(** {2 InnerClasses attribute information} *)

(** Inner class information. FIXME: provide more information. Attached
    to [InnerClasses] attributes; see the {!Classfile.attribute} type
    below. *)
type inner_class_info =
    { inner_info  : Constpool.index option
    ; outer_info  : Constpool.index option
    ; inner_name  : Constpool.index option
    ; inner_flags : AccessFlags.class_flags
    }

(** {2 LineNumberTable attribute information} *)

(** Mapping between bytecode offsets and source code line numbers for
    use by debuggers. Attached to [LineNumberTable] attribute; see the
    {!Classfile.attribute} type below. *)
type line_number_info =
    { ln_start : u2
    ; ln_line  : u2
    }

(** {2 LocalVariableTable attribute information} *)

(** Local variable name information for debugging. Attached to
    [LocalVariableTable] attribute; see the {!Classfile.attribute}
    type below. *)
type local_var_info =
    { lv_start  : u2 (** offset in the bytecode *)
    ; lv_length : u2 (** offset in the bytecode *)
    ; lv_name   : Constpool.index
    ; lv_desc   : Constpool.index
    ; lv_index  : u2 (** local variable number *)
    }

(**{2 LocalVariableTypeTable attribute information} *)

(** Local variable type information for debugging. Attached to
    [LocalVariableTypeTable] attribute; see the {!Classfile.attribute}
    type below. *)
type local_var_type_info =
    { vt_start  : u2 (** offset in the bytecode *)
    ; vt_length : u2 (** offset in the bytecode *)
    ; vt_name   : Constpool.index
    ; vt_sign   : Constpool.index
    ; vt_index  : u2 (** local variable number *)
    }

(**{2 StackMapTable attribute information}

   [StackMapTable] is a new attribute introduced in Java 6. It should
   only be attached to [Code] attributes. They provide type
   information for the operand stack and local variables within
   bytecode. This is used to do single-pass verification by
   typechecking. *)

(** Verification types. These are the possible types of members of the
    stack and local variables used by the type checking verifier. *)
type vtype_info =
    Top_vi
  | Integer_vi
  | Float_vi
  | Long_vi
  | Double_vi
  | Null_vi
  | UninitializedThis_vi
  | Object_vi of Constpool.index
  | Uninitialized_vi of u2 (** bytecode offset of the [new] instruction *)

(** Stack map frames. These are positioned in the bytecode and used by
    the typechecker to verify the bytecode. The [_extended] variants
    have been removed since they are inserted automatically as needed
    by {!ClassfileOutput.write_classfile}. *)
type stack_map_frame =
    Same_frame
  | Same_locals_1_stk of vtype_info
  | Chop_frame of int
  | Append_frame of vtype_info list
  | Full_frame of vtype_info list * vtype_info list
      (* ext subsumed *)

(**{2 CLDC StackMap attribute information} 

   [StackMap] is an older version of [StackMapTable] used in the CLDC
   specification.
*)

type cldc_stack_map_frame =
    CLDC_full_frame of vtype_info list * vtype_info list

(**{2 Annotation attribute information}

   Annotations were introduced in Java 5. They provide a way to
   attached user-defined information to entities within [.class] files.
*)

(** Constructors indicating the types of constants within
    annotations. *)
type constant_type =
  | Byte
  | Char
  | Double
  | Float
  | Int
  | Long
  | Short
  | Bool
  | String

(** An element within an annotation *)
type element =
  | Const_Value of constant_type * Constpool.index        (** (type_tag, cp index) *)
  | Enum_Const_Value of Constpool.index * Constpool.index (** (type_name, const_name) *)
  | Class_Info  of Constpool.index
  | Annot_Value of annotation
  | Array_Value of element list

(** Annotations themselves. An annotation consists of a pointer to the
    type of the annotation and a list of name-element pairs for the
    parameters of the annotation. *)
and annotation =
    Constpool.index *
      (Constpool.index * element) list

(**{2 Attributes}

   Representation of attibutes in [.class] files. The common part of
   all attributes is the constant pool index pointing to the name of
   the attribute. This is factored into the {!Classfile.attribute}
   type, containing the constant pool index, and the
   {!Classfile.attribute_detail} type, containing the information on
   each attribute. Note that the [.class] file writing functions in
   {!ClassfileOutput} do not check that the linked name matches the
   attribute information itself.
*)

(* See section 4.8 of the JVM spec for details of these *)

(** Pair of a constant pool index for the attribute's type and the
    attribute information itself. *)
type attribute =
  | Attribute of Constpool.index * attribute_detail

(** Specific information for attributes. *)
and attribute_detail =
  | Attr_ConstantValue of
      Constpool.index                (** index of value *)
  | Attr_Code of 
      u2
      * u2
      * LowlevelBytecode.instr option array
      * exn_hdl list
      * attribute list
	(** (max_stack, max_locals, code, handlers, attributes) *)
  | Attr_Exceptions of
      Constpool.index list (** list of checked exceptions a method may throw *)
  | Attr_InnerClasses of
      inner_class_info list   (* info about inner classes *)
  | Attr_EnclosingMethod of
      Constpool.index
      * Constpool.index option       (** (enclosing class, enclosing method) *)
  | Attr_Synthetic
  | Attr_Signature of
      Constpool.index                (* signature *)
  | Attr_SourceFile of
      Constpool.index                (* source file name *)
  | Attr_SourceDebugExtension of
      string                  (* debugging information *)
  | Attr_LineNumberTable of
      line_number_info list   (* line number table *)
  | Attr_LocalVariableTable of
      local_var_info list     (* local variable table *)
  | Attr_LocalVariableTypeTable of
      local_var_type_info list (* local variable types *)
  | Attr_Deprecated
  | Attr_RuntimeVisibleAnnotations of
      annotation list
  | Attr_RuntimeInvisibleAnnotations of
      annotation list
  | Attr_RuntimeVisibleParameterAnnotations of
      annotation list list
  | Attr_RuntimeInvisibleParameterAnnotations of
      annotation list list
  | Attr_AnnotationDefault of
      element
  | Attr_StackMapTable of
      (u2 * stack_map_frame) list
  | Attr_StackMap of           (* CLDC style stack maps *)
      (u2 * cldc_stack_map_frame) list
  | Attr of
      string
	(** provided for user-defined attributes *)

(**{2 Methods and fields}

   Methods and fields in a [.class] file are represented as values of
   the following types. *)

(** Low-level field declarations. *)
type field_decl =
    { f_flags : AccessFlags.field_flags
    ; f_name  : Constpool.index
    ; f_desc  : Constpool.index
    ; f_attrs : attribute list
    }

(** Low-level method declarations. *)
type method_decl =
    { m_flags : AccessFlags.method_flags
    ; m_name  : Constpool.index
    ; m_desc  : Constpool.index
    ; m_attrs : attribute list
    }

(**{2 Class files}

   FIXME: information about allowable major and minor numbers
*)

(** Low-level representation of Java [.class] files. *)
type class_file =
    { minor   : u2
    ; major   : u2
    ; pool    : Constpool.pool
    ; flags   : AccessFlags.class_flags
    ; this    : Constpool.index
    ; super   : Constpool.index option
    ; ifcs    : Constpool.index list
    ; fields  : field_decl list
    ; methods : method_decl list
    ; attrs   : attribute list
    }

val string_of_attr: attribute -> string

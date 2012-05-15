(* Classfile.ml
 *
 * K. MacKenzie
 * May 2006
 *)

module CP = Constpool

type u2 = int

type exn_hdl =
    { exn_start : u2
    ; exn_end   : u2
    ; exn_pc    : u2
    ; exn_type  : CP.index option
    }

type inner_class_info =
    { inner_info  : CP.index option
    ; outer_info  : CP.index option
    ; inner_name  : CP.index option
    ; inner_flags : AccessFlags.class_flags
    }

type line_number_info =
    { ln_start : u2
    ; ln_line  : u2
    }

type local_var_info =
    { lv_start  : u2
    ; lv_length : u2
    ; lv_name   : CP.index
    ; lv_desc   : CP.index
    ; lv_index  : u2
    }

type local_var_type_info =
    { vt_start  : u2
    ; vt_length : u2
    ; vt_name   : CP.index
    ; vt_sign   : CP.index
    ; vt_index  : u2
    }

type vtype_info =
    Top_vi
  | Integer_vi
  | Float_vi
  | Long_vi
  | Double_vi
  | Null_vi
  | UninitializedThis_vi
  | Object_vi of CP.index
  | Uninitialized_vi of u2 (* Location of corresponding 'new' opcode *)


type stack_map_frame =
    Same_frame
  | Same_locals_1_stk of vtype_info
  | Chop_frame of int
  | Append_frame of vtype_info list
  | Full_frame of vtype_info list * vtype_info list
(* ext subsumed *)

type cldc_stack_map_frame =
  CLDC_full_frame of vtype_info list * vtype_info list

type constant_type =
    Byte
  | Char
  | Double
  | Float
  | Int
  | Long
  | Short
  | Bool
  | String

type element =
     Const_Value of constant_type * CP.index      (* (type_tag, cp index) *)
   | Enum_Const_Value of CP.index * CP.index    (* (type_name, const_name) *)
   | Class_Info  of CP.index
   | Annot_Value of annotation
   | Array_Value of element list

and annotation =
    CP.index *                    (* type index *)
      (CP.index * element) list   (* [(name_index, value), ...] *)

(* The attribute type contained anonymous record types with
   shared field names in SML,  but we've had to use tuples in ocaml *)
(* See section 4.8 of the JVM spec for details of these *)

type attribute =
  | Attribute of CP.index * attribute_detail
and attribute_detail =
  | Attr_ConstantValue of
      CP.index                (* index of value *)
  | Attr_Code of 
      u2                      (* max_stack *)
      * u2                    (* max_locals *)
      * LowlevelBytecode.instr option array (* the instructions *)
      * exn_hdl list          (* exception handlers *)
      * attribute list        (* attributes *)
  | Attr_Exceptions of
      CP.index list           (* checked exceptions thrown by method *)
  | Attr_InnerClasses of
      inner_class_info list   (* info about inner classes *)
  | Attr_EnclosingMethod of
      CP.index                (* enclosing class *)
      * CP.index option       (* enclosing method *)
  | Attr_Synthetic
  | Attr_Signature of
      CP.index                (* signature *)
  | Attr_SourceFile of
      CP.index                (* source file name *)
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

type field_decl =
    { f_flags : AccessFlags.field_flags
    ; f_name  : CP.index
    ; f_desc  : CP.index
    ; f_attrs : attribute list
    }

type method_decl =
    { m_flags : AccessFlags.method_flags
    ; m_name  : CP.index
    ; m_desc  : CP.index
    ; m_attrs : attribute list
    }

type class_file =
    { minor   : u2
    ; major   : u2
    ; pool    : CP.pool
    ; flags   : AccessFlags.class_flags
    ; this    : CP.index
    ; super   : CP.index option
    ; ifcs    : CP.index list
    ; fields  : field_decl list
    ; methods : method_decl list
    ; attrs   : attribute list
    }

let string_of_attr (Attribute(_,attribute_detail)) = (* kwxm: debugging *)
  match attribute_detail with 
  | Attr_ConstantValue _ -> "Attr_ConstantValue"
  | Attr_Code _ -> "Attr_Code"
  | Attr_Exceptions _ -> "Attr_Exceptions"
  | Attr_InnerClasses _ -> "Attr_InnerClasses"
  | Attr_EnclosingMethod _ -> "Attr_EnclosingMethod"
  | Attr_Synthetic -> "Attr_Synthetic"
  | Attr_Signature _ -> "Attr_Signature"
  | Attr_SourceFile _ -> "Attr_SourceFile"
  | Attr_SourceDebugExtension _ -> "Attr_SourceDebugExtension"
  | Attr_LineNumberTable _ -> "Attr_LineNumberTable"
  | Attr_LocalVariableTable _ -> "Attr_LocalVariableTable"
  | Attr_LocalVariableTypeTable _ -> "Attr_LocalVariableTypeTable"
  | Attr_Deprecated -> "Attr_Deprecated"
  | Attr_RuntimeVisibleAnnotations _ -> "Attr_RuntimeVisibleAnnotations"
  | Attr_RuntimeInvisibleAnnotations _ -> "Attr_RuntimeInvisibleAnnotations"
  | Attr_RuntimeVisibleParameterAnnotations _ -> "Attr_RuntimeVisibleParameterAnnotations"
  | Attr_RuntimeInvisibleParameterAnnotations _ -> "Attr_RuntimeInvisibleParameterAnnotations"
  | Attr_AnnotationDefault _ -> "Attr_AnnotationDefault"
  | Attr_StackMapTable _ -> "Attr_StackMapTable"
  | Attr_StackMap _ -> "Attr_StackMap"
  | Attr s -> "ATTR " ^ s


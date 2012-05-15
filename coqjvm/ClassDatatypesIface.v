Require Import OrderedTypeEx.
Require Import StoreIface.
Require Import BasicMachineTypes.
Require Import AnnotationIface.
Require Import List.
Require Import ZArith.

Module Type CLASSDATATYPES
  (C_B : BASICS)
  (C_A : ANNOTATION C_B).

(***************************
 * Various notions of type
 ***************************)
Inductive array_type : Set :=
 aty_boolean | aty_char | aty_float | aty_double | aty_byte | aty_short | aty_int | aty_long : array_type.

Inductive stack_type : Set :=
 sty_int | sty_long | sty_double | sty_float | sty_addr.

Inductive java_type : Set :=
| ty_byte
| ty_char
| ty_double
| ty_float
| ty_int
| ty_long
| ty_boolean
| ty_short : java_type
| ty_ref : java_ref_type -> java_type
with java_ref_type : Set :=
| ty_obj : C_B.Classname.t -> java_ref_type
| ty_arr : java_type -> java_ref_type.

Declare Module JavaType_as_UOT : UsualOrderedType with Definition t := java_type.

Inductive value_category : Set := category1 | category2.

Definition java_type_category : java_type -> value_category :=
  fun ty => match ty with
  | ty_byte => category1
  | ty_char => category1
  | ty_short => category1
  | ty_boolean => category1
  | ty_int => category1
  | ty_float => category1
  | ty_ref _ => category1
  | ty_double => category2
  | ty_long => category2
  end.

Definition stack_type_category : stack_type -> value_category :=
  fun ty => match ty with
  | sty_int => category1
  | sty_float => category1
  | sty_double => category2
  | sty_addr => category1
  | sty_long => category2
  end.

(**********************
 * The instructions
 **********************)

(* Constants *)
Inductive double_constant : Set := d0 | d1 : double_constant.
Inductive float_constant : Set := f0 | f1 | f2 : float_constant.
Inductive long_constant : Set := l0 | l1 : long_constant.

(* Comparison operations *)
Inductive acmp : Set := acmp_eq | acmp_ne : acmp.
Inductive cmp : Set := cmp_eq | cmp_ne | cmp_lt | cmp_ge | cmp_gt | cmp_le : cmp.
Inductive float_cmp_opt : Set := fcmp_l | fcmp_g : float_cmp_opt.

(* Arithmetic operations *)
Inductive integer_bop : Set :=
 iadd | idiv | iand | imul | ior | irem | ishl | ishr | isub | iushr | ixor : integer_bop.

Inductive integer_uop : Set :=
 ineg : integer_uop.

Inductive float_bop : Set :=
 fadd | fdiv | fmul | frem | fsub : float_bop.

Inductive float_uop : Set :=
 fneg : float_uop.

Inductive opcode : Set :=
(* Arithmetic *)
| op_iarithb : integer_bop -> opcode
| op_iarithu : integer_uop -> opcode
| op_larithb : integer_bop -> opcode
| op_larithu : integer_uop -> opcode
| op_iinc    : nat -> C_B.Int32.t -> opcode
| op_darithb : float_bop -> opcode
| op_darithu : float_uop -> opcode
| op_farithb : float_bop -> opcode
| op_farithu : float_uop -> opcode

(* Stack Operations *)
| op_dup     : opcode
| op_dup_x1  : opcode
| op_dup_x2  : opcode
| op_dup2    : opcode
| op_dup2_x1 : opcode
| op_dup2_x2 : opcode
| op_nop     : opcode
| op_pop     : opcode
| op_pop2    : opcode
| op_swap    : opcode

(* Local Variables *)
| op_load   : stack_type -> nat -> opcode
| op_store  : stack_type -> nat -> opcode

(* OO *)
| op_instanceof      : C_B.ConstantPoolRef.t -> opcode
| op_invokeinterface : C_B.ConstantPoolRef.t -> opcode
| op_invokespecial   : C_B.ConstantPoolRef.t -> opcode
| op_invokestatic    : C_B.ConstantPoolRef.t -> opcode
| op_invokevirtual   : C_B.ConstantPoolRef.t -> opcode
| op_aconst_null     : opcode
| op_checkcast       : C_B.ConstantPoolRef.t -> opcode
| op_getfield        : C_B.ConstantPoolRef.t -> opcode
| op_getstatic       : C_B.ConstantPoolRef.t -> opcode
| op_new             : C_B.ConstantPoolRef.t -> opcode
| op_putfield        : C_B.ConstantPoolRef.t -> opcode
| op_putstatic       : C_B.ConstantPoolRef.t -> opcode

(* Comparisons and flow control *)
| op_if_acmp : acmp -> Z -> opcode
| op_if_icmp : cmp -> Z -> opcode
| op_if      : cmp -> Z -> opcode
| op_ifnonnull : Z -> opcode
| op_ifnull  : Z -> opcode
| op_goto    : Z -> opcode
| op_valreturn : stack_type -> opcode
| op_return  : opcode
| op_athrow  : opcode
| op_dcmp    : float_cmp_opt -> opcode
| op_fcmp    : float_cmp_opt -> opcode
| op_lcmp    : opcode
| op_lookupswitch : Z -> Z -> list (Z * Z) -> opcode
| op_tableswitch : Z -> Z -> Z -> list Z -> opcode

(* Arrays *)
| op_iaload  : opcode
| op_iastore : opcode
| op_aaload  : opcode
| op_aastore : opcode
| op_anewarray : C_B.ConstantPoolRef.t -> opcode
| op_arraylength : opcode
| op_baload  : opcode
| op_bastore : opcode
| op_caload  : opcode
| op_castore : opcode
| op_daload  : opcode
| op_dastore : opcode
| op_faload  : opcode
| op_fastore : opcode
| op_laload  : opcode
| op_lastore : opcode
| op_multianewarray : C_B.ConstantPoolRef.t -> nat -> opcode
| op_newarray : array_type -> opcode
| op_saload  : opcode
| op_sastore : opcode

(* Constants *)
| op_iconst : C_B.Int32.t -> opcode
| op_dconst : double_constant -> opcode
| op_fconst : float_constant -> opcode
| op_lconst : long_constant -> opcode
| op_ldc    : C_B.ConstantPoolRef.t -> opcode
| op_ldc2   : C_B.ConstantPoolRef.t -> opcode

(* Concurrency *)
| op_monitorenter : opcode
| op_monitorexit  : opcode

(* Conversions *)
| op_i2b    : opcode
| op_i2c    : opcode
| op_i2d    : opcode
| op_i2f    : opcode
| op_i2l    : opcode
| op_i2s    : opcode
| op_d2f    : opcode
| op_d2i    : opcode
| op_d2l    : opcode
| op_f2d    : opcode
| op_f2i    : opcode
| op_f2l    : opcode
| op_l2d    : opcode
| op_l2f    : opcode
| op_l2i    : opcode.

(*************************
 * Some functions for dealing with the program counter
 *************************)
Parameter pc_plus_offset : nat -> Z -> option nat.
(* for checking if the current program counter is in the range of an exception handler *)
Parameter is_within : forall s e p, ({p >= s /\ p < e} + {p < s \/ p >= e})%nat.

(*************************
 * The structure of classes
 *************************)
Record descriptor : Set := mkDescriptor
 { descriptor_ret_type : option java_type
 ; descriptor_arg_types : list java_type
 }.

Declare Module Descriptor_as_UOT : UsualOrderedType with Definition t := descriptor.

Record exception_handler : Set := mkExcHandler
  { exc_start_pc : nat
  ; exc_end_pc   : nat
  ; exc_handler_pc : nat
  ; exc_catch_type : option C_B.ConstantPoolRef.t
  }.

Record precode : Type := mkPreCode
  { precode_max_stack       : nat
  ; precode_max_lvars       : nat
  ; precode_code            : list opcode            (* FIXME: need a better representation than lists *)
  ; precode_exception_table : list exception_handler
  ; precode_annot           : C_A.code_annotation
  }. (* + certificate *)

Record code : Set := mkCode
  { code_max_stack       : nat
  ; code_max_lvars       : nat
  ; code_code            : list opcode            (* FIXME: need a better representation than lists *)
  ; code_exception_table : list exception_handler
  }. (* + certificate *)

Record premethod : Type := mkPreMethod
  { premethod_name         : C_B.Methodname.t
  ; premethod_descriptor   : descriptor
  ; premethod_public       : bool
  ; premethod_protected    : bool
  ; premethod_private      : bool
  ; premethod_abstract     : bool (* if this is false, and the code does not exist, then the method is native *)
  ; premethod_static       : bool
  ; premethod_final        : bool
  ; premethod_synchronized : bool
  ; premethod_strict       : bool
  ; premethod_code         : option precode
  ; premethod_annot        : C_A.method_annotation
  }. (* + attributes *)

Record method : Type := mkMethod
  { method_name         : C_B.Methodname.t
  ; method_descriptor   : descriptor
  ; method_public       : bool
  ; method_protected    : bool
  ; method_private      : bool
  ; method_abstract     : bool (* if this is false, and the code does not exist, then the method is native *)
  ; method_static       : bool
  ; method_final        : bool
  ; method_synchronized : bool
  ; method_strict       : bool
  ; method_code         : option code
  ; method_annot        : C_A.method_annotation
  }. (* + attributes *)

Declare Module MethodList : STORE with Definition key := (C_B.Methodname.t * descriptor)%type
                                  with Definition object := method
                                  with Definition Key.eq := (@eq (C_B.Methodname.t * descriptor)).

Record field : Set := mkField
  { field_name      : C_B.Fieldname.t
  ; field_type      : java_type
  ; field_public    : bool
  ; field_private   : bool
  ; field_protected : bool
  ; field_static    : bool
  ; field_final     : bool
  ; field_volatile  : bool
  ; field_transient : bool
  }. (* + attributes (ConstantValue) *)

Declare Module FieldList : STORE with Definition key := (C_B.Fieldname.t * java_type)%type
                                 with Definition object := field.

Inductive constantpool_entry : Set :=
| cpe_methodref : C_B.Classname.t -> C_B.Methodname.t -> descriptor -> constantpool_entry
| cpe_interfacemethodref : C_B.Classname.t -> C_B.Methodname.t -> descriptor -> constantpool_entry
| cpe_fieldref  : C_B.Classname.t -> C_B.Fieldname.t -> java_type -> constantpool_entry
| cpe_int       : C_B.Int32.t -> constantpool_entry
| cpe_classref  : C_B.Classname.t -> constantpool_entry
| cpe_other     : constantpool_entry.

Declare Module ConstantPool : STORE with Definition key := C_B.ConstantPoolRef.t
                                    with Definition object := constantpool_entry.

Record preclass : Type := mkPreClass
  { preclass_name         : C_B.Classname.t
  ; preclass_super_name   : option C_B.Classname.t
  ; preclass_super_interfaces : list C_B.Classname.t
  ; preclass_public       : bool
  ; preclass_final        : bool
  ; preclass_super        : bool
  ; preclass_interface    : bool
  ; preclass_abstract     : bool
  ; preclass_methods      : list premethod
  ; preclass_fields       : FieldList.t
  ; preclass_constantpool : ConstantPool.t
  ; preclass_annotation   : C_A.class_annotation
  }. (* + attributes *)

Record class : Type := mkClass
  { class_name         : C_B.Classname.t
  ; class_super_class  : option C_B.Classname.t
  ; class_interfaces   : list C_B.Classname.t
  ; class_public       : bool
  ; class_final        : bool
  ; class_super        : bool
  ; class_interface    : bool
  ; class_abstract     : bool
  ; class_methods      : MethodList.t
  ; class_fields       : FieldList.t
  ; class_constantpool : ConstantPool.t
  }. (* + attributes *)

Inductive has_premethod : list premethod -> C_B.Methodname.t * descriptor -> premethod -> Prop :=
| has_premethod_cons_1 : forall nm d public protected private abstract static final synchronized strict code annot meths,
   has_premethod (mkPreMethod nm d public protected private abstract static final synchronized strict code annot::meths)
                 (nm,d)
                 (mkPreMethod nm d public protected private abstract static final synchronized strict code annot)
| has_premethod_cons_2 : forall nm d public protected private abstract static final synchronized strict code annot meths nm' d' m,
   has_premethod meths (nm',d') m ->
   (nm <> nm' \/ d <> d') ->
   has_premethod (mkPreMethod nm d public protected private abstract static final synchronized strict code annot::meths)
                 (nm',d')
                 m.

Hypothesis has_premethod_dec : forall ms mdesc,
 (exists m, has_premethod ms mdesc m)\/(forall m, ~has_premethod ms mdesc m).

Hypothesis has_premethod_functional : forall ms mdesc mA mB,
 has_premethod ms mdesc mA ->
 has_premethod ms mdesc mB ->
 mA = mB.

Hypothesis has_premethod_in : forall ms m,
  has_premethod ms (premethod_name m, premethod_descriptor m) m ->
  In m ms.

Hypothesis has_premethod_name : forall ms md m,
  has_premethod ms md m -> md = (premethod_name m, premethod_descriptor m).
Implicit Arguments has_premethod_name [ms md m].

End CLASSDATATYPES.












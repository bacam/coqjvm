Require BasicMachineTypes.
Require Import ZArith.
Require Import List.

Module InstructionSet (B:BasicMachineTypes.BASICS).

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

Inductive array_type : Set :=
 aty_boolean | aty_char | aty_float | aty_double | aty_byte | aty_short | aty_int | aty_long : array_type.

Inductive stack_type : Set :=
 sty_int | sty_long | sty_double | sty_float | sty_addr.

Inductive opcode : Set :=
(* Arithmetic *)
| op_iarithb : integer_bop -> opcode
| op_iarithu : integer_uop -> opcode
| op_larithb : integer_bop -> opcode
| op_larithu : integer_uop -> opcode
| op_iinc    : nat -> B.Int32.t -> opcode
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
| op_instanceof      : B.ConstantPoolRef.t -> opcode
| op_invokeinterface : B.ConstantPoolRef.t -> opcode
| op_invokespecial   : B.ConstantPoolRef.t -> opcode
| op_invokestatic    : B.ConstantPoolRef.t -> opcode
| op_invokevirtual   : B.ConstantPoolRef.t -> opcode
| op_aconst_null     : opcode
| op_checkcast       : B.ConstantPoolRef.t -> opcode
| op_getfield        : B.ConstantPoolRef.t -> opcode
| op_getstatic       : B.ConstantPoolRef.t -> opcode
| op_new             : B.ConstantPoolRef.t -> opcode
| op_putfield        : B.ConstantPoolRef.t -> opcode
| op_putstatic       : B.ConstantPoolRef.t -> opcode

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
| op_anewarray : opcode
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
| op_multianewarray : nat -> nat -> opcode
| op_newarray : array_type -> opcode
| op_saload  : opcode
| op_sastore : opcode

(* Constants *)
| op_iconst : B.Int32.t -> opcode
| op_dconst : double_constant -> opcode
| op_fconst : float_constant -> opcode
| op_lconst : long_constant -> opcode
| op_ldc    : B.ConstantPoolRef.t -> opcode
| op_ldc2   : B.ConstantPoolRef.t -> opcode

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

Definition pc_plus_offset : nat -> Z -> option nat :=
  fun pc offset =>
  match (Z_of_nat pc + offset)%Z with
  | Z0 => Some 0
  | Zpos p => Some (nat_of_P p)
  | Zneg _ => None
  end.

End InstructionSet.
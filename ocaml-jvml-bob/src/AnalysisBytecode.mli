type instr =
    Aaload
  | Aastore
  | Aconst_null
  | Aload of int
  | Anewarray of Jvmtype.jclass
  | Areturn
  | Arraylength
  | Astore of int
  | Athrow
  | Baload
  | Bastore
  | Caload
  | Castore
  | Checkcast of Jvmtype.jref_type
  | Classconst of Jvmtype.jref_type
  | D2f
  | D2i
  | D2l
  | Dadd
  | Daload
  | Dastore
  | Dcmpg
  | Dcmpl
  | Dconst of float
  | Ddiv
  | Dload of int
  | Dmul
  | Dneg
  | Drem
  | Dreturn
  | Dstore of int
  | Dsub
  | Dup
  | Dup_x1
  | Dup_x2
  | Dup2
  | Dup2_x1
  | Dup2_x2
  | F2d
  | F2i
  | F2l
  | Fadd
  | Faload
  | Fastore
  | Fcmpg
  | Fcmpl
  | Fconst of JFloat.t
  | Fdiv
  | Fload of int
  | Fmul
  | Fneg
  | Frem
  | Freturn
  | Fstore of int
  | Fsub
  | Getfield of Jvmtype.jclass * string * Jvmtype.jtype
  | Getstatic of Jvmtype.jclass * string * Jvmtype.jtype
  | Goto of int
  | I2b
  | I2c
  | I2d
  | I2f
  | I2l
  | I2s
  | Iadd
  | Iaload
  | Iand
  | Iastore
  | Iconst of int32
  | Idiv
  | If_acmpeq of int
  | If_acmpne of int
  | If_icmpeq of int
  | If_icmpne of int
  | If_icmplt of int
  | If_icmpge of int
  | If_icmpgt of int
  | If_icmple of int
  | Ifeq of int
  | Ifne of int
  | Iflt of int
  | Ifge of int
  | Ifgt of int
  | Ifle of int
  | Ifnonnull of int
  | Ifnull of int
  | Iinc of int * int
  | Iload of int
  | Imul
  | Ineg
  | Instanceof of Jvmtype.jclass
  | Invokeinterface of Jvmtype.jclass * string * Jvmtype.methodsig
  | Invokespecial of Jvmtype.jref_type * string * Jvmtype.methodsig
  | Invokestatic of Jvmtype.jref_type * string * Jvmtype.methodsig
  | Invokevirtual of Jvmtype.jref_type * string * Jvmtype.methodsig
  | Ior
  | Irem
  | Ireturn
  | Ishl
  | Ishr
  | Istore of int
  | Isub
  | Iushr
  | Ixor
  | Jsr of int
  | L2d
  | L2f
  | L2i
  | Ladd
  | Laload
  | Land
  | Lastore
  | Lcmp
  | Lconst of int64
  | Ldiv
  | Lload of int
  | Lmul
  | Lneg
  | Lookupswitch of int * (int32 * int) list
  | Lor
  | Lrem
  | Lreturn
  | Lshl
  | Lshr
  | Lstore of int
  | Lsub
  | Lushr
  | Lxor
  | Monitorenter
  | Monitorexit
  | New of Jvmtype.jclass
  | Nop
  | Pop
  | Pop2
  | Putfield of Jvmtype.jclass * string * Jvmtype.jtype
  | Putstatic of Jvmtype.jclass * string * Jvmtype.jtype
  | Ret of int
  | Return
  | Saload
  | Sastore
  | Sconst of string
  | Swap
  | Tableswitch of int * int32 * int list

exception TranslationError of string

val of_lowlevel_bytecode : Constpool.pool -> LowlevelBytecode.instr option array -> instr array

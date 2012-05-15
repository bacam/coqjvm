(** The type of JVM instructions and functions for reading and writing
    arrays of instructions to bytecode

    @author Robert Atkey
*)

(**{1 Representation of JVM instructions and bytecode}

   We represent JVM instructions in memory by members of the [instr]
   type below. A sequence of instructions, as in the [Code] attribute
   for methods is represented as a [instr option array]. Within this
   array instructions are located at the same byte offset as they
   would be in the bytecode. Offsets that are inside other
   instructions are represented by [None]. This representation is used
   to preserve the offsets within the instructions. 
*)

(**{2 Types} *)
(** Types of array that can be constructed by the [newarray]
    instruction *)
type array_type =
  | Array_boolean
  | Array_char
  | Array_float
  | Array_double
  | Array_byte
  | Array_int
  | Array_short
  | Array_long

(** The JVM instruction set. There is a one-to-one relationship
    between JVM instructions and the constructors of this type. See
    the Java Virtual Machine specification for more details. Each of
    the instructions that takes an [int] field has an additional
    comment explaining the size constraints on this argument. All
    [int32] fields are signed. *)
type instr =
    (* A *)
  | Aaload
  | Aastore
  | Aconst_null
  | Aload of int (** unsigned byte *)
  | Aload_w of int (** unsigned 16bit *)
  | Aload_0
  | Aload_1
  | Aload_2
  | Aload_3
  | Anewarray of Constpool.index
  | Areturn
  | Arraylength
  | Astore of int (** unsigned byte *)
  | Astore_w of int (** unsigned 16bit *)
  | Astore_0
  | Astore_1
  | Astore_2
  | Astore_3
  | Athrow
      (* B *)
  | Baload
  | Bastore
  | Bipush of int (** signed byte *)
      (* C *)
  | Caload
  | Castore
  | Checkcast of Constpool.index
      (* D *)
  | D2f
  | D2i
  | D2l
  | Dadd
  | Daload
  | Dastore
  | Dcmpg
  | Dcmpl
  | Dconst_0
  | Dconst_1
  | Ddiv
  | Dload of int (** unsigned byte *)
  | Dload_w of int (** unsigned 16bit *)
  | Dload_0
  | Dload_1
  | Dload_2
  | Dload_3
  | Dmul
  | Dneg
  | Drem
  | Dreturn
  | Dstore of int (** unsigned byte *)
  | Dstore_w of int (** unsigned 16bit *)
  | Dstore_0
  | Dstore_1
  | Dstore_2
  | Dstore_3
  | Dsub
  | Dup
  | Dup_x1
  | Dup_x2
  | Dup2
  | Dup2_x1
  | Dup2_x2
      (* F *)
  | F2d
  | F2i
  | F2l
  | Fadd
  | Faload
  | Fastore
  | Fcmpg
  | Fcmpl
  | Fconst_0
  | Fconst_1
  | Fconst_2
  | Fdiv
  | Fload of int (** unsigned byte *)
  | Fload_w of int (** unsigned 16bit *)
  | Fload_0
  | Fload_1
  | Fload_2
  | Fload_3
  | Fmul
  | Fneg
  | Frem
  | Freturn
  | Fstore of int (** unsigned byte *)
  | Fstore_w of int (** unsigned 16bit *)
  | Fstore_0
  | Fstore_1
  | Fstore_2
  | Fstore_3
  | Fsub
      (* G *)
  | Getfield of Constpool.index
  | Getstatic of Constpool.index
  | Goto of int (** signed 16bit *)
  | Goto_w of int32 (** signed 32bit *)
      (* I *)
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
  | Iconst_m1
  | Iconst_0
  | Iconst_1
  | Iconst_2
  | Iconst_3
  | Iconst_4
  | Iconst_5
  | Idiv
  | If_acmpeq of int (** signed 16bit *)
  | If_acmpne of int (** signed 16bit *)
  | If_icmpeq of int (** signed 16bit *)
  | If_icmpne of int (** signed 16bit *)
  | If_icmplt of int (** signed 16bit *)
  | If_icmpge of int (** signed 16bit *)
  | If_icmpgt of int (** signed 16bit *)
  | If_icmple of int (** signed 16bit *)
  | Ifeq of int (** signed 16bit *)
  | Ifne of int (** signed 16bit *)
  | Iflt of int (** signed 16bit *)
  | Ifge of int (** signed 16bit *)
  | Ifgt of int (** signed 16bit *)
  | Ifle of int (** signed 16bit *)
  | Ifnonnull of int (** signed 16bit *)
  | Ifnull of int (** signed 16bit *)
  | Iinc of int * int (** unsigned byte * signed byte *)
  | Iinc_w of int * int (** unsigned 16bit * signed 16bit *)
  | Iload of int (** unsigned byte *)
  | Iload_w of int (** unsigned 16bit *)
  | Iload_0
  | Iload_1
  | Iload_2
  | Iload_3
  | Imul
  | Ineg
  | Instanceof of Constpool.index
  | Invokeinterface of Constpool.index * int (** unsigned byte, must not be zero *)
  | Invokespecial of Constpool.index
  | Invokestatic of Constpool.index
  | Invokevirtual of Constpool.index
  | Ior
  | Irem
  | Ireturn
  | Ishl
  | Ishr
  | Istore of int (** unsigned byte *)
  | Istore_w of int (** unsigned 16bit *)
  | Istore_0
  | Istore_1
  | Istore_2
  | Istore_3
  | Isub
  | Iushr
  | Ixor
      (* J *)
  | Jsr of int (** signed 16bit *)
  | Jsr_w of int32 (** signed 32bit *)
      (* L *)
  | L2d
  | L2f
  | L2i
  | Ladd
  | Laload
  | Land
  | Lastore
  | Lcmp
  | Lconst_0
  | Lconst_1
  | Ldc of Constpool.index (** unsigned byte *)
  | Ldc_w of Constpool.index (** unsigned 16bit *)
  | Ldc2_w of Constpool.index (** unsigned 16bit *)
  | Ldiv
  | Lload of int (** unsigned byte *)
  | Lload_w of int (** unsigned 16bit *)
  | Lload_0
  | Lload_1
  | Lload_2
  | Lload_3
  | Lmul
  | Lneg
  | Lookupswitch of int32 (** signed 32bit *) * (int32 * int32) list
  | Lor
  | Lrem
  | Lreturn
  | Lshl
  | Lshr
  | Lstore of int (** unsigned byte *)
  | Lstore_w of int (** unsigned 16bit *)
  | Lstore_0
  | Lstore_1
  | Lstore_2
  | Lstore_3
  | Lsub
  | Lushr
  | Lxor
      (* M *)
  | Monitorenter
  | Monitorexit
  | Multianewarray of Constpool.index * int (** unsigned byte *)
      (* N *)
  | New of Constpool.index
  | Newarray of array_type
  | Nop
      (* P *)
  | Pop
  | Pop2
  | Putfield of Constpool.index
  | Putstatic of Constpool.index
      (* R *)
  | Ret of int (** unsigned byte *)
  | Ret_w of int (** unsigned 16bit *)
  | Return
      (* S *)
  | Saload
  | Sastore
  | Sipush of int (** signed 16bit *)
  | Swap
      (* T *)
  | Tableswitch of int32 * int32 * int32 list

(**{2 Functions} *)

(** Exception thrown for invalid bytecode *)
exception Invalid_bytecode of string

(** Calculate the length, in bytes, of the bytecode representation of
    the given instruction. The offset is required in order to compute the
    padding required to 32bit-word align the [lookupswitch] and
    [tableswitch] instructions. *)
val instruction_length : instr:instr -> offset:int -> int

(** Read a stream of bytecode instructions from [input], of length
    [length] and return the output in the format described above. This
    function raises {!LowlevelBytecode.Invalid_bytecode} if the stream is
    not valid. *)
val read_code : input:IO.input -> length:int -> instr option array

(** Write the instructions in [instrs] (which must be in the
    representation above) to [output] as bytecode. {b BUG}: does not
    currently check that the spaces between instructions are actually
    [None], and may output more bytes than the length of [instrs] if
    the last instruction is too long. *)
val write_code : instrs:instr option array -> output:'a IO.output -> unit

val string_of_opcode: instr -> string
(** Convert opcode to string.  For debugging purposes. *)

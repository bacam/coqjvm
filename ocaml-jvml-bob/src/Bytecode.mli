(** High-level bytecode instructions *)

(**{1 High-level bytecode instructions}

   This module contains the definition of high-level bytecode
   instructions. There are four principal differences between these and
   the low-level instructions in {!LowlevelBytecode}:

   {ul
   {- There are no references to a constant pool; all external
   references are included inline. Small integer constants are
   compiled to the smallest instruction that fits.}
   {- There are no bytecode offsets in the branching instructions,
   these are replaced by references to labels (defined in {!Label})
   and a pseudo-instruction [Jlabel].}
   {- The labels themselves are annotated with values of some
   type ['a], this is used to provide typing information with lists of
   bytecode instructions.}
   {- There is a single instruction for constructing new
   arrays. This is compiled into the appropriate instruction based on
   the type of the array.}}

   The module {!CompileBytecode} translates lists of these high-level
   instructions into low-level instructions.
*)

(**{2 Instructions} *)

(** High-level bytecode instructions. *)
type 'a instr =
    | Jlabel of Label.label * 'a
    | Jaaload
    | Jaastore
    | Jaconst_null
    | Jaload of int
    | Jarraylength
    | Jastore of int
    | Jathrow
    | Jbaload
    | Jbastore
    | Jcaload
    | Jcastore
    | Jcheckcast of Jvmtype.jref_type
    | Jclassconst of Jvmtype.jref_type
    | Jd2f
    | Jd2i
    | Jd2l
    | Jdadd
    | Jdaload
    | Jdastore
    | Jdcmpg
    | Jdcmpl
    | Jdconst of float
    | Jddiv
    | Jdload of int
    | Jdmul
    | Jdneg
    | Jdrem
    | Jdstore of int
    | Jdsub
    | Jdup
    | Jdup_x1
    | Jdup_x2
    | Jdup2
    | Jdup2_x1
    | Jdup2_x2
    | Jf2d
    | Jf2i
    | Jf2l
    | Jfadd
    | Jfaload
    | Jfastore
    | Jfcmpg
    | Jfcmpl
    | Jfconst of JFloat.t
    | Jfdiv
    | Jfload of int
    | Jfmul
    | Jfneg
    | Jfrem
    | Jfstore of int
    | Jfsub
    | Jgetfield of Jvmtype.jclass * string * Jvmtype.jtype
    | Jgetstatic of Jvmtype.jclass * string * Jvmtype.jtype
    | Jgoto of Label.label
    | Ji2b
    | Ji2c
    | Ji2d
    | Ji2f
    | Ji2l
    | Ji2s
    | Jiadd
    | Jiaload
    | Jiand
    | Jiastore
    | Jiconst of int32
    | Jidiv
    | Jif_acmpeq of Label.label
    | Jif_acmpne of Label.label
    | Jif_icmpeq of Label.label
    | Jif_icmpne of Label.label
    | Jif_icmplt of Label.label
    | Jif_icmpge of Label.label
    | Jif_icmpgt of Label.label
    | Jif_icmple of Label.label
    | Jifeq of Label.label
    | Jifne of Label.label
    | Jiflt of Label.label
    | Jifge of Label.label
    | Jifgt of Label.label
    | Jifle of Label.label
    | Jifnonnull of Label.label
    | Jifnull of Label.label
    | Jiinc of int * int
    | Jiload of int
    | Jimul
    | Jineg
    | Jinstanceof of Jvmtype.jref_type
    | Jinvokeinterface of Jvmtype.jclass * string * Jvmtype.methodsig
    | Jinvokespecial of Jvmtype.jref_type * string * Jvmtype.methodsig
    | Jinvokestatic of Jvmtype.jref_type * string * Jvmtype.methodsig
    | Jinvokevirtual of Jvmtype.jref_type * string * Jvmtype.methodsig
    | Jior
    | Jirem
    | Jishl
    | Jishr
    | Jistore of int
    | Jisub
    | Jiushr
    | Jixor
    | Jjsr of Label.label
    | Jl2d
    | Jl2f
    | Jl2i
    | Jladd
    | Jlaload
    | Jland
    | Jlastore
    | Jlcmp
    | Jlconst of int64
    | Jldiv
    | Jlload of int
    | Jlmul
    | Jlneg
    | Jlookupswitch of Label.label * (int32 * Label.label) list
    | Jlor
    | Jlrem
    | Jlshl
    | Jlshr
    | Jlstore of int
    | Jlsub
    | Jlushr
    | Jlxor
    | Jmonitorenter
    | Jmonitorexit
    | Jnew of Jvmtype.jclass
    | Jnewarray of Jvmtype.jtype * int
    | Jnop
    | Jpop
    | Jpop2
    | Jputfield of Jvmtype.jclass * string * Jvmtype.jtype
    | Jputstatic of Jvmtype.jclass * string * Jvmtype.jtype
    | Jret of int
    | Jreturn
    | Jsaload
    | Jsastore
    | Jsconst of string
    | Jswap
    | Jtableswitch of Label.label * int32 * Label.label list

(** Dump a list of instructions to the standard out. *)
val printInstrs : 'a instr list -> unit

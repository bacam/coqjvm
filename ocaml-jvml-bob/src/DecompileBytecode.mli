(** Decompilation of low-level JVM instructions to high-level
    instructions *)

(**{1 Low to high-level JVM instruction stream decompilation}

   This module performs contains a function to compile instruction
   sequences containing low-level instructions as defined in
   {!LowlevelBytecode}, to the representation of high-level
   instructions in {!Bytecode}. It is the inverse to the routines in
   {!CompileBytecode}. *)

(** Exception indicating when the bytecode being decompiled is
    incorrect in some way. The string argument gives the details. *)
exception DecompileBytecodeError of string

(**{2 Mapping offsets to labels} *)

(** Type of objects maintaining a mapping between bytecode offsets and
    {!Label.label} labels. *)
type label_map_builder

(** Creation of an empty mapping between offsets and labels. *)
val create_label_map_builder : unit -> label_map_builder

(** Add a mapping of a given bytecode offset to a label. If the offset
    has not been used before then a fresh label is generated,
    otherwise the previously used label is returned. *)
val decompile_offset : label_map_builder -> int -> Label.label

(**{2 Decompilation of bytecode} *)

(** [decompile_bytecode pool label_map instrs] returns the decompiled
    instructions from [instrs]. Labels are inserted into the
    decompiled bytecode if required by internal jumps within the
    bytecode or if a mapping is present in [label_map]. The constant
    pool [pool] is used to resolve constants used in the bytecode. *)
val decompile_bytecode : Constpool.pool -> label_map_builder -> LowlevelBytecode.instr option array -> unit Bytecode.instr list

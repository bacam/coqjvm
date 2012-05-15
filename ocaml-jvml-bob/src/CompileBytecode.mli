(** Compilation of high-level JVM instructions to low-level
    instructions *)

(**{1 High to low-level JVM instruction compilation}

   This module performs contains a function to compile instruction
   sequences containing high-level instructions with labels as defined
   in {!Bytecode}, to the representation of low-level instructions in
   {!LowlevelBytecode}. It is the inverse to the routines in
   {!DecompileBytecode}. *)

(** Exception indicating when the bytecode being compiled is incorrect
    in some way. The string argument gives details. *)
exception CompileBytecodeError of string

(** Compile the high-level instructions in [instrs] into an array of
    low-level instructions suitable for
    {!LowlevelBytecode.write_code}. The function also requires a
    {!Constpool.builder} object [cp_builder] for adding constants
    within the bytecode to, and the optional return type of the method
    containing this code, for resolving the return instructions in
    [instrs]. The function also returns a hash table mapping labels
    found in [instrs] to offsets in the low-level bytecode. *)
val compile_bytecode :
  builder:Constpool.builder ->
  return_typ:Jvmtype.jtype option ->
  instrs:'a Bytecode.instr list ->
  LowlevelBytecode.instr option array * (Label.label, int) Hashtbl.t

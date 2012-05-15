exception Invalid_bytecode of string

module CP = Constpool

type index = CP.index

type array_type =
  | Array_boolean
  | Array_char
  | Array_float
  | Array_double
  | Array_byte
  | Array_int
  | Array_short
  | Array_long

type instr =
    (* A *)
  | Aaload
  | Aastore
  | Aconst_null
  | Aload of int (* unsigned byte *)
  | Aload_w of int (* unsigned 16bit *)
  | Aload_0
  | Aload_1
  | Aload_2
  | Aload_3
  | Anewarray of index
  | Areturn
  | Arraylength
  | Astore of int (* unsigned byte *)
  | Astore_w of int (* unsigned 16bit *)
  | Astore_0
  | Astore_1
  | Astore_2
  | Astore_3
  | Athrow
      (* B *)
  | Baload
  | Bastore
  | Bipush of int (* byte *)
      (* C *)
  | Caload
  | Castore
  | Checkcast of index
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
  | Dload of int (* unsigned byte *)
  | Dload_w of int (* unsigned 16bit *)
  | Dload_0
  | Dload_1
  | Dload_2
  | Dload_3
  | Dmul
  | Dneg
  | Drem
  | Dreturn
  | Dstore of int (* unsigned byte *)
  | Dstore_w of int (* unsigned 16bit *)
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
  | Fload of int (* unsigned byte *)
  | Fload_w of int (* unsigned 16bit *)
  | Fload_0
  | Fload_1
  | Fload_2
  | Fload_3
  | Fmul
  | Fneg
  | Frem
  | Freturn
  | Fstore of int (* unsigned byte *)
  | Fstore_w of int (* unsigned 16bit *)
  | Fstore_0
  | Fstore_1
  | Fstore_2
  | Fstore_3
  | Fsub
      (* G *)
  | Getfield of index
  | Getstatic of index
  | Goto of int (* signed 16bit *)
  | Goto_w of int32 (* signed 32bit *)
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
  | If_acmpeq of int (* signed 16bit *)
  | If_acmpne of int (* signed 16bit *)
  | If_icmpeq of int (* signed 16bit *)
  | If_icmpne of int (* signed 16bit *)
  | If_icmplt of int (* signed 16bit *)
  | If_icmpge of int (* signed 16bit *)
  | If_icmpgt of int (* signed 16bit *)
  | If_icmple of int (* signed 16bit *)
  | Ifeq of int (* signed 16bit *)
  | Ifne of int (* signed 16bit *)
  | Iflt of int (* signed 16bit *)
  | Ifge of int (* signed 16bit *)
  | Ifgt of int (* signed 16bit *)
  | Ifle of int (* signed 16bit *)
  | Ifnonnull of int (* signed 16bit *)
  | Ifnull of int (* signed 16bit *)
  | Iinc of int (* unsigned byte *) * int (* signed byte *)
  | Iinc_w of int (* unsigned 16bit *) * int (* signed 16bit *)
  | Iload of int (* unsigned byte *)
  | Iload_w of int (* unsigned 16bit *)
  | Iload_0
  | Iload_1
  | Iload_2
  | Iload_3
  | Imul
  | Ineg
  | Instanceof of index
  | Invokeinterface of index * int (* unsigned byte, must not be zero *)
  | Invokespecial of index
  | Invokestatic of index
  | Invokevirtual of index
  | Ior
  | Irem
  | Ireturn
  | Ishl
  | Ishr
  | Istore of int (* unsigned byte *)
  | Istore_w of int (* unsigned 16bit *)
  | Istore_0
  | Istore_1
  | Istore_2
  | Istore_3
  | Isub
  | Iushr
  | Ixor
      (* J *)
  | Jsr of int (* signed 16bit *)
  | Jsr_w of int32 (* signed 32bit *)
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
  | Ldc of index (* unsigned byte *)
  | Ldc_w of index (* unsigned 16bit *)
  | Ldc2_w of index (* unsigned 16bit *)
  | Ldiv
  | Lload of int (* unsigned byte *)
  | Lload_w of int (* unsigned 16bit *)
  | Lload_0
  | Lload_1
  | Lload_2
  | Lload_3
  | Lmul
  | Lneg
  | Lookupswitch of int32 (* signed 32bit *) * (int32 * int32) list
  | Lor
  | Lrem
  | Lreturn
  | Lshl
  | Lshr
  | Lstore of int (* unsigned byte *)
  | Lstore_w of int (* unsigned 16bit *)
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
  | Multianewarray of index * int (* unsigned byte *)
      (* N *)
  | New of index
  | Newarray of array_type
  | Nop
      (* P *)
  | Pop
  | Pop2
  | Putfield of index
  | Putstatic of index
      (* R *)
  | Ret of int (* unsigned byte *)
  | Ret_w of int (* unsigned 16bit *)
  | Return
      (* S *)
  | Saload
  | Sastore
  | Sipush of int (* signed 16bit *)
  | Swap
      (* T *)
  | Tableswitch of int32 * int32 * int32 list


(* this function computes the padding required by the lookupswitch and
   tableswitch instructions *)
let padding offset = (4 - ((offset + 1) mod 4)) mod 4

let instruction_length ~instr ~offset = match instr with
  | Aaload | Aastore | Aconst_null | Aload_0 | Aload_1 | Aload_2 | Aload_3 | Areturn
  | Arraylength | Astore_0 | Astore_1 | Astore_2 | Astore_3 | Athrow | Baload
  | Bastore | Caload | Castore | D2f | D2i | D2l | Dadd | Daload | Dastore | Dcmpg
  | Dcmpl | Dconst_0 | Dconst_1 | Ddiv | Dload_0 | Dload_1 | Dload_2 | Dload_3
  | Dmul | Dneg | Drem | Dreturn | Dstore_0 | Dstore_1 | Dstore_2 | Dstore_3
  | Dsub | Dup | Dup_x1 | Dup_x2 | Dup2 | Dup2_x1 | Dup2_x2 | F2d | F2i | F2l
  | Fadd | Faload | Fastore | Fcmpg | Fcmpl | Fconst_0 | Fconst_1 | Fconst_2
  | Fdiv | Fload_0 | Fload_1 | Fload_2 | Fload_3 | Fmul | Fneg | Frem | Freturn
  | Fstore_0 | Fstore_1 | Fstore_2 | Fstore_3 | Fsub | I2b | I2c | I2d | I2f | I2l
  | I2s | Iadd | Iaload | Iand | Iastore | Iconst_m1 | Iconst_0 | Iconst_1 | Iconst_2
  | Iconst_3 | Iconst_4 | Iconst_5 | Idiv | Iload_0 | Iload_1 | Iload_2 | Iload_3
  | Imul | Ineg | Ior | Irem | Ireturn | Ishl | Ishr | Istore_0 | Istore_1 | Istore_2
  | Istore_3 | Isub | Iushr | Ixor | L2d | L2f | L2i | Ladd | Laload | Land | Lastore
  | Lcmp | Lconst_0 | Lconst_1 | Ldiv | Lload_0 | Lload_1 | Lload_2 | Lload_3 | Lmul
  | Lneg | Lor | Lrem | Lreturn | Lshl | Lshr | Lstore_0 | Lstore_1 | Lstore_2 | Lstore_3
  | Lsub | Lushr | Lxor | Monitorenter | Monitorexit | Nop | Pop | Pop2 | Return
  | Saload | Sastore | Swap ->
      1
  | Aload _ | Astore _ | Bipush _ | Dload _ | Dstore _ | Fload _ | Fstore _
  | Iload _ | Istore _ | Ldc _ | Lload _ | Lstore _ | Newarray _ | Ret _ ->
      2
  | Anewarray _ | Checkcast _ | Getfield _ | Getstatic _ | Goto _ | If_acmpeq _
  | If_acmpne _ | If_icmpeq _ | If_icmpne _ | If_icmplt _ | If_icmpge _ | If_icmpgt _ 
  | If_icmple _ | Ifeq _ | Ifne _ | Iflt _ | Ifge _ | Ifgt _ | Ifle _ | Ifnonnull _ 
  | Ifnull _ | Iinc (_,_) | Instanceof _ | Invokespecial _ | Invokestatic _
  | Invokevirtual _ | Jsr _ | Ldc_w _ | Ldc2_w _ | New _ | Putfield _ | Putstatic _
  | Sipush _ ->
      3
  | Aload_w _ | Astore_w _ | Dload_w _ | Dstore_w _ | Fload_w _ | Fstore_w _
  | Iload_w _ | Istore_w _ | Lload_w _ | Lstore_w _ | Ret_w _  | Multianewarray (_,_) ->
      4
  | Goto_w _ | Invokeinterface (_,_) | Jsr_w _ ->
      5
  | Iinc_w (_,_) ->
      6
  | Lookupswitch (default, pairs) ->
      1 + padding offset + 8 + List.length pairs * 8 (* FIXME: overflow? *)
  | Tableswitch (default, low, list) ->
      1 + padding offset + 12 + List.length list * 4 (* FIXME: overflow? *)

let read_opcode ~input ~offset =
  let opcode = IO.read_byte input in match opcode with
    | 0x32 -> Aaload
    | 0x53 -> Aastore
    | 0x01 -> Aconst_null
    | 0x19 -> let lvar_idx = IO.read_byte input in Aload lvar_idx
    | 0x2a -> Aload_0
    | 0x2b -> Aload_1
    | 0x2c -> Aload_2
    | 0x2d -> Aload_3
    | 0xbd -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Anewarray cp_idx
    | 0xb0 -> Areturn
    | 0xbe -> Arraylength
    | 0x3a -> let lvar_idx = IO.read_byte input in Astore lvar_idx
    | 0x4b -> Astore_0
    | 0x4c -> Astore_1
    | 0x4d -> Astore_2
    | 0x4e -> Astore_3
    | 0xbf -> Athrow

    | 0x33 -> Baload
    | 0x54 -> Bastore
    | 0x10 -> let const = IO.read_byte input in Bipush const (* FIXME: this is probably wrong: should be signed byte, but round-tripping works because we make the same mistake below *)

    | 0x34 -> Caload
    | 0x55 -> Castore
    | 0xc0 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Checkcast cp_idx

    | 0x90 -> D2f
    | 0x8e -> D2i
    | 0x8f -> D2l
    | 0x63 -> Dadd
    | 0x31 -> Daload
    | 0x52 -> Dastore
    | 0x98 -> Dcmpg
    | 0x97 -> Dcmpl
    | 0x0e -> Dconst_0
    | 0x0f -> Dconst_1
    | 0x6f -> Ddiv
    | 0x18 -> let lvar_idx = IO.read_byte input in Dload lvar_idx
    | 0x26 -> Dload_0
    | 0x27 -> Dload_1
    | 0x28 -> Dload_2
    | 0x29 -> Dload_3
    | 0x6b -> Dmul
    | 0x77 -> Dneg
    | 0x73 -> Drem
    | 0xaf -> Dreturn
    | 0x39 -> let lvar_idx = IO.read_byte input in Dstore lvar_idx
    | 0x47 -> Dstore_0
    | 0x48 -> Dstore_1
    | 0x49 -> Dstore_2
    | 0x4a -> Dstore_3
    | 0x67 -> Dsub
    | 0x59 -> Dup
    | 0x5a -> Dup_x1
    | 0x5b -> Dup_x2
    | 0x5c -> Dup2
    | 0x5d -> Dup2_x1
    | 0x5e -> Dup2_x2

    | 0x8d -> F2d
    | 0x8b -> F2i
    | 0x8c -> F2l
    | 0x62 -> Fadd
    | 0x30 -> Faload
    | 0x51 -> Fastore
    | 0x96 -> Fcmpg
    | 0x95 -> Fcmpl
    | 0x0b -> Fconst_0
    | 0x0c -> Fconst_1
    | 0x0d -> Fconst_2
    | 0x6e -> Fdiv
    | 0x17 -> let lvar_idx = IO.read_byte input in Fload lvar_idx
    | 0x22 -> Fload_0
    | 0x23 -> Fload_1
    | 0x24 -> Fload_2
    | 0x25 -> Fload_3
    | 0x6a -> Fmul
    | 0x76 -> Fneg
    | 0x72 -> Frem
    | 0xae -> Freturn
    | 0x38 -> let lvar_idx = IO.read_byte input in Fstore lvar_idx
    | 0x43 -> Fstore_0;
    | 0x44 -> Fstore_1;
    | 0x45 -> Fstore_2;
    | 0x46 -> Fstore_3;
    | 0x66 -> Fsub;

    | 0xb4 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Getfield cp_idx
    | 0xb2 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Getstatic cp_idx
    | 0xa7 -> let offset = IO.BigEndian.read_i16 input in Goto offset
    | 0xc8 -> let offset = IO.BigEndian.read_real_i32 input in Goto_w offset;

    | 0x91 -> I2b
    | 0x92 -> I2c
    | 0x87 -> I2d
    | 0x86 -> I2f
    | 0x85 -> I2l
    | 0x93 -> I2s
    | 0x60 -> Iadd
    | 0x2e -> Iaload
    | 0x7e -> Iand
    | 0x4f -> Iastore
    | 0x02 -> Iconst_m1
    | 0x03 -> Iconst_0
    | 0x04 -> Iconst_1
    | 0x05 -> Iconst_2
    | 0x06 -> Iconst_3
    | 0x07 -> Iconst_4
    | 0x08 -> Iconst_5
    | 0x6c -> Idiv
    | 0xa5 -> let offset = IO.BigEndian.read_i16 input in If_acmpeq offset
    | 0xa6 -> let offset = IO.BigEndian.read_i16 input in If_acmpne offset
    | 0x9f -> let offset = IO.BigEndian.read_i16 input in If_icmpeq offset
    | 0xa0 -> let offset = IO.BigEndian.read_i16 input in If_icmpne offset
    | 0xa1 -> let offset = IO.BigEndian.read_i16 input in If_icmplt offset
    | 0xa2 -> let offset = IO.BigEndian.read_i16 input in If_icmpge offset
    | 0xa3 -> let offset = IO.BigEndian.read_i16 input in If_icmpgt offset
    | 0xa4 -> let offset = IO.BigEndian.read_i16 input in If_icmple offset
    | 0x99 -> let offset = IO.BigEndian.read_i16 input in Ifeq offset
    | 0x9a -> let offset = IO.BigEndian.read_i16 input in Ifne offset
    | 0x9b -> let offset = IO.BigEndian.read_i16 input in Iflt offset
    | 0x9c -> let offset = IO.BigEndian.read_i16 input in Ifge offset
    | 0x9d -> let offset = IO.BigEndian.read_i16 input in Ifgt offset
    | 0x9e -> let offset = IO.BigEndian.read_i16 input in Ifle offset
    | 0xc7 -> let offset = IO.BigEndian.read_i16 input in Ifnonnull offset
    | 0xc6 -> let offset = IO.BigEndian.read_i16 input in Ifnull offset
    | 0x84 ->
	let lvar_idx = IO.read_byte input in
	let const = IO.read_signed_byte input in
	  Iinc (lvar_idx, const)
    | 0x15 -> let lvar_idx = IO.read_byte input in Iload lvar_idx
    | 0x1a -> Iload_0
    | 0x1b -> Iload_1
    | 0x1c -> Iload_2
    | 0x1d -> Iload_3
    | 0x68 -> Imul
    | 0x74 -> Ineg
    | 0xc1 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Instanceof cp_idx
    | 0xb9 ->
	let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in
	let count = IO.read_byte input in
	let should_be_zero = IO.read_byte input in
	  if count = 0 then raise (Invalid_bytecode "invokeinterface: count should be > 0");
	  if should_be_zero <> 0 then raise (Invalid_bytecode "invokeinterface: 4th byte should be 0");
	  Invokeinterface (cp_idx,count);
    | 0xb7 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Invokespecial cp_idx
    | 0xb8 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Invokestatic cp_idx
    | 0xb6 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Invokevirtual cp_idx
    | 0x80 -> Ior
    | 0x70 -> Irem
    | 0xac -> Ireturn
    | 0x78 -> Ishl
    | 0x7a -> Ishr
    | 0x36 -> let lvar_idx = IO.read_byte input in Istore lvar_idx
    | 0x3b -> Istore_0
    | 0x3c -> Istore_1
    | 0x3d -> Istore_2
    | 0x3e -> Istore_3
    | 0x64 -> Isub
    | 0x7c -> Iushr
    | 0x82 -> Ixor

    | 0xa8 -> let offset = IO.BigEndian.read_i16 input in Jsr offset
    | 0xc9 -> let offset = IO.BigEndian.read_real_i32 input in Jsr_w offset

    | 0x8a -> L2d
    | 0x89 -> L2f
    | 0x88 -> L2i
    | 0x61 -> Ladd
    | 0x2f -> Laload
    | 0x7f -> Land
    | 0x50 -> Lastore
    | 0x94 -> Lcmp
    | 0x09 -> Lconst_0
    | 0x0a -> Lconst_1
    | 0x12 -> let cp_idx = CP.index_of_int (IO.read_byte input) in Ldc cp_idx
    | 0x13 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Ldc_w cp_idx
    | 0x14 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Ldc2_w cp_idx
    | 0x6d -> Ldiv
    | 0x16 -> let lvar_idx = IO.read_byte input in Lload lvar_idx
    | 0x1e -> Lload_0
    | 0x1f -> Lload_1
    | 0x20 -> Lload_2
    | 0x21 -> Lload_3
    | 0x69 -> Lmul
    | 0x75 -> Lneg
    | 0xab ->
	Util.repeat (padding offset) (fun () -> let _ = IO.read_byte input in ());
	let default = IO.BigEndian.read_real_i32 input in
	let len = IO.BigEndian.read_real_i32 input in
	  (* next test is OK because code arrays can only be 2^16 long *)
	let _ = if len > 0xffffl then raise (Invalid_bytecode "read_opcode: lookupswitch: length greater than 0xffff") in
	let _ = if len < 0l then raise (Invalid_bytecode "read_opcode: lookupswitch: length less than 0") in
	let pairs =
	  Util.repeat_collect (Int32.to_int len)
	    (fun () ->
	       let matchn = IO.BigEndian.read_real_i32 input in
	       let offset = IO.BigEndian.read_real_i32 input in
		 (matchn, offset))
	in
	  Lookupswitch (default, pairs)
    | 0x81 -> Lor
    | 0x71 -> Lrem
    | 0xad -> Lreturn
    | 0x79 -> Lshl
    | 0x7b -> Lshr
    | 0x37 -> let lvar_idx = IO.read_byte input in Lstore lvar_idx
    | 0x3f -> Lstore_0
    | 0x40 -> Lstore_1
    | 0x41 -> Lstore_2
    | 0x42 -> Lstore_3
    | 0x65 -> Lsub
    | 0x7d -> Lushr
    | 0x83 -> Lxor

    | 0xc2 -> Monitorenter
    | 0xc3 -> Monitorexit
    | 0xc5 -> 
	let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in
	let dim = IO.read_byte input in
	  Multianewarray (cp_idx, dim)

    | 0xbb -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in New cp_idx
    | 0xbc ->
	let type_code = IO.read_byte input in 
	let typ = match type_code with
	  | 4 -> Array_boolean
	  | 5 -> Array_char
	  | 6 -> Array_float
	  | 7 -> Array_double
	  | 8 -> Array_byte
	  | 9 -> Array_short
	  | 10 -> Array_int
	  | 11 -> Array_long
	  | _ -> raise (Invalid_bytecode (Printf.sprintf "read_opcode: newarray invalid type code %d" type_code))
	in
	  Newarray typ
    | 0x00 -> Nop

    | 0x57 -> Pop
    | 0x58 -> Pop2
    | 0xb5 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Putfield cp_idx
    | 0xb3 -> let cp_idx = CP.index_of_int (IO.BigEndian.read_ui16 input) in Putstatic cp_idx

    | 0xa9 -> let lvar_idx = IO.read_byte input in Ret lvar_idx
    | 0xb1 -> Return

    | 0x35 -> Saload
    | 0x56 -> Sastore
    | 0x11 -> let const = IO.BigEndian.read_i16 input in Sipush const
    | 0x5f -> Swap

    | 0xaa ->
	Util.repeat (padding offset) (fun () -> let _ = IO.read_byte input in ());
	let default = IO.BigEndian.read_real_i32 input in
	let low = IO.BigEndian.read_real_i32 input in
	let high = IO.BigEndian.read_real_i32 input in
	let _ = if low > high then raise (Invalid_bytecode "read_opcode: tableswitch low > high") in
	let len = Int32.add (Int32.sub high low) 1l in
	let _ = if len > 0xffffl then raise (Invalid_bytecode "read_opcode: tableswitch high - low + 1 is greater than 0xffff") in
	let _ = if len < 0l then raise (Invalid_bytecode "read_opcode: tableswitch high - low + 1 is less than 0") in
	let offsets = Util.repeat_collect (Int32.to_int len) (fun () -> IO.BigEndian.read_real_i32 input) in
	  Tableswitch (default, low, offsets)

    | 0xc4 ->
	(let opcode2 = IO.read_byte input in match opcode2 with
	   | 0x15 -> let lvar_idx = IO.BigEndian.read_ui16 input in Iload_w lvar_idx
	   | 0x36 -> let lvar_idx = IO.BigEndian.read_ui16 input in Istore_w lvar_idx
	   | 0x17 -> let lvar_idx = IO.BigEndian.read_ui16 input in Fload_w lvar_idx
	   | 0x38 -> let lvar_idx = IO.BigEndian.read_ui16 input in Fstore_w lvar_idx
	   | 0x19 -> let lvar_idx = IO.BigEndian.read_ui16 input in Aload_w lvar_idx
	   | 0x3a -> let lvar_idx = IO.BigEndian.read_ui16 input in Astore_w lvar_idx
	   | 0x18 -> let lvar_idx = IO.BigEndian.read_ui16 input in Dload_w lvar_idx
	   | 0x39 -> let lvar_idx = IO.BigEndian.read_ui16 input in Dstore_w lvar_idx
	   | 0x16 -> let lvar_idx = IO.BigEndian.read_ui16 input in Lload_w lvar_idx
	   | 0x37 -> let lvar_idx = IO.BigEndian.read_ui16 input in Lstore_w lvar_idx
	   | 0xa9 -> let lvar_idx = IO.BigEndian.read_ui16 input in Ret_w lvar_idx
	   | 0x84 ->
	       let lvar_idx = IO.BigEndian.read_ui16 input in
	       let const = IO.BigEndian.read_i16 input in
		 Iinc_w (lvar_idx, const)
	   | _ -> raise (Invalid_bytecode (Printf.sprintf "read_opcode: Invalid wide opcode: 0x%02X" opcode2)))
    | _ -> raise (Invalid_bytecode (Printf.sprintf "read_opcode: Invalid opcode: 0x%02X" opcode))

let read_code ~input ~length =
  let instrs = Array.make length None in
  let input = Util.IO.limited_input length input in
  let rec decode_loop idx =
    if idx > length then
      raise (Invalid_bytecode "Bytecode too long for the length") (* should never happen due to limited_input *)
    else if idx = length then
      ()
    else
      let instr = read_opcode input idx in
	instrs.(idx) <- Some instr;
	decode_loop (idx + instruction_length instr idx)
  in
    (try
       decode_loop 0;
     with IO.No_more_input -> raise (Invalid_bytecode "Bytecode length incorrect"));
    instrs

let write_opcode ~instr ~idx output =
  let write_signed_byte b = if b < -0x80 || b > 0x7f then raise (IO.Overflow "Overflow in write_signed_byte") else IO.write_byte output b in
  let write_byte b = if b < 0 || b > 0xff then raise (IO.Overflow "Overflow in write_byte") else IO.write_byte output b in
  let write_opcode code = write_byte code in
  let write_opcode_byte code arg = write_byte code; write_byte arg in (* FIXME: check for overflow before write_byte *)
  let write_opcode_idx code idx = write_byte code; IO.BigEndian.write_ui16 output (CP.index_to_int idx) in
  let write_opcode_offset code offset = write_byte code; IO.BigEndian.write_i16 output offset in
  let write_opcode_wide_offset code offset = write_byte code; IO.BigEndian.write_real_i32 output offset in
  let write_wide_opcode code arg = write_byte 0xc4; write_byte code; IO.BigEndian.write_ui16 output arg in
    match instr with
      | Aaload        -> write_opcode 0x32
      | Aastore       -> write_opcode 0x53
      | Aconst_null   -> write_opcode 0x01
      | Aload idx     -> write_opcode_byte 0x19 idx
      | Aload_w idx   -> write_wide_opcode 0x19 idx
      | Aload_0       -> write_opcode 0x2a
      | Aload_1       -> write_opcode 0x2b
      | Aload_2       -> write_opcode 0x2c
      | Aload_3       -> write_opcode 0x2d
      | Anewarray idx -> write_opcode_idx 0xbd idx
      | Areturn       -> write_opcode 0xb0
      | Arraylength   -> write_opcode 0xbe
      | Astore lvar   -> write_opcode_byte 0x3a lvar
      | Astore_w lvar -> write_wide_opcode 0x3a lvar
      | Astore_0      -> write_opcode 0x4b
      | Astore_1      -> write_opcode 0x4c
      | Astore_2      -> write_opcode 0x4d
      | Astore_3      -> write_opcode 0x4e
      | Athrow        -> write_opcode 0xbf

      | Baload        -> write_opcode 0x33
      | Bastore       -> write_opcode 0x54
      | Bipush k      -> write_opcode_byte 0x10 k

      | Caload        -> write_opcode 0x34
      | Castore       -> write_opcode 0x55
      | Checkcast idx -> write_opcode_idx 0xc0 idx

      | D2f           -> write_opcode 0x90
      | D2i           -> write_opcode 0x8e
      | D2l           -> write_opcode 0x8f
      | Dadd          -> write_opcode 0x63
      | Daload        -> write_opcode 0x31
      | Dastore       -> write_opcode 0x52
      | Dcmpg         -> write_opcode 0x98
      | Dcmpl         -> write_opcode 0x97
      | Dconst_0      -> write_opcode 0x0e
      | Dconst_1      -> write_opcode 0x0f
      | Ddiv          -> write_opcode 0x6f
      | Dload lvar    -> write_opcode_byte 0x18 lvar
      | Dload_w lvar  -> write_wide_opcode 0x18 lvar
      | Dload_0       -> write_opcode 0x26
      | Dload_1       -> write_opcode 0x27
      | Dload_2       -> write_opcode 0x28
      | Dload_3       -> write_opcode 0x29
      | Dmul          -> write_opcode 0x6b
      | Dneg          -> write_opcode 0x77
      | Drem          -> write_opcode 0x73
      | Dreturn       -> write_opcode 0xaf
      | Dstore lvar   -> write_opcode_byte 0x39 lvar
      | Dstore_w lvar -> write_wide_opcode 0x39 lvar
      | Dstore_0      -> write_opcode 0x47
      | Dstore_1      -> write_opcode 0x48
      | Dstore_2      -> write_opcode 0x49
      | Dstore_3      -> write_opcode 0x4a
      | Dsub          -> write_opcode 0x67
      | Dup           -> write_opcode 0x59
      | Dup_x1        -> write_opcode 0x5a
      | Dup_x2        -> write_opcode 0x5b
      | Dup2          -> write_opcode 0x5c
      | Dup2_x1       -> write_opcode 0x5d
      | Dup2_x2       -> write_opcode 0x5e

      | F2d           -> write_opcode 0x8d
      | F2i           -> write_opcode 0x8b
      | F2l           -> write_opcode 0x8c
      | Fadd          -> write_opcode 0x62
      | Faload        -> write_opcode 0x30
      | Fastore       -> write_opcode 0x51
      | Fcmpg         -> write_opcode 0x96
      | Fcmpl         -> write_opcode 0x95
      | Fconst_0      -> write_opcode 0x0b
      | Fconst_1      -> write_opcode 0x0c
      | Fconst_2      -> write_opcode 0x0d
      | Fdiv          -> write_opcode 0x6e
      | Fload lvar    -> write_opcode_byte 0x17 lvar
      | Fload_w lvar  -> write_wide_opcode 0x17 lvar
      | Fload_0       -> write_opcode 0x22
      | Fload_1       -> write_opcode 0x23
      | Fload_2       -> write_opcode 0x24
      | Fload_3       -> write_opcode 0x25
      | Fmul          -> write_opcode 0x6a
      | Fneg          -> write_opcode 0x76
      | Frem          -> write_opcode 0x72
      | Freturn       -> write_opcode 0xae
      | Fstore lvar   -> write_opcode_byte 0x38 lvar
      | Fstore_w lvar -> write_wide_opcode 0x38 lvar
      | Fstore_0      -> write_opcode 0x43
      | Fstore_1      -> write_opcode 0x44
      | Fstore_2      -> write_opcode 0x45
      | Fstore_3      -> write_opcode 0x46
      | Fsub          -> write_opcode 0x66

      | Getfield idx  -> write_opcode_idx 0xb4 idx
      | Getstatic idx -> write_opcode_idx 0xb2 idx
      | Goto offset   -> write_opcode_offset 0xa7 offset
      | Goto_w offset -> write_opcode_wide_offset 0xc8 offset

      | I2b           -> write_opcode 0x91
      | I2c           -> write_opcode 0x92
      | I2d           -> write_opcode 0x87
      | I2f           -> write_opcode 0x86
      | I2l           -> write_opcode 0x85
      | I2s           -> write_opcode 0x93
      | Iadd          -> write_opcode 0x60
      | Iaload        -> write_opcode 0x2e
      | Iand          -> write_opcode 0x7e
      | Iastore       -> write_opcode 0x4f
      | Iconst_m1     -> write_opcode 0x02
      | Iconst_0      -> write_opcode 0x03
      | Iconst_1      -> write_opcode 0x04
      | Iconst_2      -> write_opcode 0x05
      | Iconst_3      -> write_opcode 0x06
      | Iconst_4      -> write_opcode 0x07
      | Iconst_5      -> write_opcode 0x08
      | Idiv          -> write_opcode 0x6c
      | If_acmpeq o   -> write_opcode_offset 0xa5 o
      | If_acmpne o   -> write_opcode_offset 0xa6 o
      | If_icmpeq o   -> write_opcode_offset 0x9f o
      | If_icmpne o   -> write_opcode_offset 0xa0 o
      | If_icmplt o   -> write_opcode_offset 0xa1 o
      | If_icmpge o   -> write_opcode_offset 0xa2 o
      | If_icmpgt o   -> write_opcode_offset 0xa3 o
      | If_icmple o   -> write_opcode_offset 0xa4 o
      | Ifeq o        -> write_opcode_offset 0x99 o
      | Ifne o        -> write_opcode_offset 0x9a o
      | Iflt o        -> write_opcode_offset 0x9b o
      | Ifge o        -> write_opcode_offset 0x9c o
      | Ifgt o        -> write_opcode_offset 0x9d o
      | Ifle o        -> write_opcode_offset 0x9e o
      | Ifnonnull o   -> write_opcode_offset 0xc7 o
      | Ifnull o      -> write_opcode_offset 0xc6 o
      | Iinc (lvar,k) ->
	  write_byte 0x84;
	  write_byte lvar;
	  write_signed_byte k
      | Iinc_w (lvar,k) ->
	  write_byte 0xc4;
	  write_byte 0x84;
	  IO.BigEndian.write_ui16 output lvar;
	  IO.BigEndian.write_i16 output k
      | Iload lvar    -> write_opcode_byte 0x15 lvar
      | Iload_w lvar  -> write_wide_opcode 0x15 lvar
      | Iload_0       -> write_opcode 0x1a
      | Iload_1       -> write_opcode 0x1b
      | Iload_2       -> write_opcode 0x1c
      | Iload_3       -> write_opcode 0x1d
      | Imul          -> write_opcode 0x68
      | Ineg          -> write_opcode 0x74
      | Instanceof i  -> write_opcode_idx 0xc1 i
      | Invokeinterface (i,c) ->
	  write_opcode_idx 0xb9 i;
	  write_byte c;
	  write_byte 0
      | Invokespecial i -> write_opcode_idx 0xb7 i
      | Invokestatic i  -> write_opcode_idx 0xb8 i
      | Invokevirtual i -> write_opcode_idx 0xb6 i
      | Ior             -> write_opcode 0x80
      | Irem            -> write_opcode 0x70
      | Ireturn         -> write_opcode 0xac
      | Ishl            -> write_opcode 0x78
      | Ishr            -> write_opcode 0x7a
      | Istore lvar     -> write_opcode_byte 0x36 lvar
      | Istore_w lvar   -> write_wide_opcode 0x36 lvar
      | Istore_0        -> write_opcode 0x3b
      | Istore_1        -> write_opcode 0x3c
      | Istore_2        -> write_opcode 0x3d
      | Istore_3        -> write_opcode 0x3e
      | Isub            -> write_opcode 0x64
      | Iushr           -> write_opcode 0x7c
      | Ixor            -> write_opcode 0x82
	  
      | Jsr offset      -> write_opcode_offset 0xa8 offset
      | Jsr_w offset    -> write_opcode_wide_offset 0xc9 offset

      | L2d             -> write_opcode 0x8a
      | L2f             -> write_opcode 0x89
      | L2i             -> write_opcode 0x88
      | Ladd            -> write_opcode 0x61
      | Laload          -> write_opcode 0x2f
      | Land            -> write_opcode 0x7f
      | Lastore         -> write_opcode 0x50
      | Lcmp            -> write_opcode 0x94
      | Lconst_0        -> write_opcode 0x09
      | Lconst_1        -> write_opcode 0x0a
      | Ldc i           -> write_opcode_byte 0x12 (CP.index_to_int i)
      | Ldc_w i         -> write_opcode_idx 0x13 i
      | Ldc2_w i        -> write_opcode_idx 0x14 i
      | Ldiv            -> write_opcode 0x6d
      | Lload lvar      -> write_opcode_byte 0x16 lvar
      | Lload_w lvar    -> write_wide_opcode 0x16 lvar
      | Lload_0         -> write_opcode 0x1e
      | Lload_1         -> write_opcode 0x1f
      | Lload_2         -> write_opcode 0x20
      | Lload_3         -> write_opcode 0x21
      | Lmul            -> write_opcode 0x69
      | Lneg            -> write_opcode 0x75
      | Lookupswitch (default, pairs) ->
	  write_opcode 0xab;
	  Util.repeat (padding idx) (fun () -> write_byte 0x00);
	  IO.BigEndian.write_real_i32 output default;
	  IO.BigEndian.write_i32 output (List.length pairs);
	  List.iter (fun (matchn,offset) ->
		       IO.BigEndian.write_real_i32 output matchn;
		       IO.BigEndian.write_real_i32 output offset)
	    pairs
      | Lor             -> write_opcode 0x81
      | Lrem            -> write_opcode 0x71
      | Lreturn         -> write_opcode 0xad
      | Lshl            -> write_opcode 0x79
      | Lshr            -> write_opcode 0x7b
      | Lstore lvar     -> write_opcode_byte 0x37 lvar
      | Lstore_w lvar   -> write_wide_opcode 0x37 lvar
      | Lstore_0        -> write_opcode 0x3f
      | Lstore_1        -> write_opcode 0x40
      | Lstore_2        -> write_opcode 0x41
      | Lstore_3        -> write_opcode 0x42
      | Lsub            -> write_opcode 0x65
      | Lushr           -> write_opcode 0x7d
      | Lxor            -> write_opcode 0x83

      | Monitorenter    -> write_opcode 0xc2
      | Monitorexit     -> write_opcode 0xc3
      | Multianewarray (idx, dim) ->
	  write_opcode_idx 0xc5 idx;
	  write_byte dim

      | New idx         -> write_opcode_idx 0xbb idx
      | Newarray typ    ->
	  write_opcode 0xbc;
	  write_byte (match typ with
	    | Array_boolean -> 4
	    | Array_char    -> 5
	    | Array_float   -> 6
	    | Array_double  -> 7
	    | Array_byte    -> 8
	    | Array_short   -> 9
	    | Array_int     -> 10
	    | Array_long    -> 11)
      | Nop             -> write_opcode 0x00

      | Pop             -> write_opcode 0x57
      | Pop2            -> write_opcode 0x58
      | Putfield i      -> write_opcode_idx 0xb5 i
      | Putstatic i     -> write_opcode_idx 0xb3 i

      | Ret lvar        -> write_opcode_byte 0xa9 lvar
      | Ret_w lvar      -> write_wide_opcode 0xa9 lvar
      | Return          -> write_opcode 0xb1

      | Saload          -> write_opcode 0x35
      | Sastore         -> write_opcode 0x56
      | Sipush k        -> write_opcode 0x11; IO.BigEndian.write_i16 output k
      | Swap            -> write_opcode 0x5f

      | Tableswitch (default, low, offsets) ->
	  let high = Int32.sub (Int32.add low (Int32.of_int (List.length offsets))) 1l in
	    write_opcode 0xaa;
	    Util.repeat (padding idx) (fun () -> write_byte 0);
	    IO.BigEndian.write_real_i32 output default;
	    IO.BigEndian.write_real_i32 output low;
	    IO.BigEndian.write_real_i32 output high;
	    List.iter (IO.BigEndian.write_real_i32 output) offsets

let write_code ~instrs ~output =
  let len = Array.length instrs in
  let output' = IO.output_string () in
  let rec loop offset =
    if offset > len then
      raise (Invalid_bytecode "Bytecode length longer than instruction array")
    else if offset = len then
      ()
    else
      match instrs.(offset) with
	| None -> failwith "write_code: Invalid bytecode array"
	| Some instr ->
	    write_opcode instr offset output';
	    (* FIXME: check that all the entries between instructions are None *)
	    loop (offset + instruction_length instr offset)
  in
  let _ = loop 0 in
  let str = IO.close_out output' in
    if String.length str != len then raise (Invalid_bytecode "Bytecode length longer than instruction array");
    IO.nwrite output str


let string_of_opcode = function
  | Aaload -> "Aaload"
  | Aastore -> "Aastore"
  | Aconst_null -> "Aconst_null"
  | Aload _  -> "Aload _"
  | Aload_w _  -> "Aload_w _"
  | Aload_0 -> "Aload_0"
  | Aload_1 -> "Aload_1"
  | Aload_2 -> "Aload_2"
  | Aload_3 -> "Aload_3"
  | Anewarray _  -> "Anewarray _"
  | Areturn -> "Areturn"
  | Arraylength -> "Arraylength"
  | Astore _  -> "Astore _"
  | Astore_w _  -> "Astore_w _"
  | Astore_0 -> "Astore_0"
  | Astore_1 -> "Astore_1"
  | Astore_2 -> "Astore_2"
  | Astore_3 -> "Astore_3"
  | Athrow -> "Athrow"
  | Baload -> "Baload"
  | Bastore -> "Bastore"
  | Bipush _  -> "Bipush _"
  | Caload -> "Caload"
  | Castore -> "Castore"
  | Checkcast _  -> "Checkcast _"
  | D2f -> "D2f"
  | D2i -> "D2i"
  | D2l -> "D2l"
  | Dadd -> "Dadd"
  | Daload -> "Daload"
  | Dastore -> "Dastore"
  | Dcmpg -> "Dcmpg"
  | Dcmpl -> "Dcmpl"
  | Dconst_0 -> "Dconst_0"
  | Dconst_1 -> "Dconst_1"
  | Ddiv -> "Ddiv"
  | Dload _  -> "Dload _"
  | Dload_w _  -> "Dload_w _"
  | Dload_0 -> "Dload_0"
  | Dload_1 -> "Dload_1"
  | Dload_2 -> "Dload_2"
  | Dload_3 -> "Dload_3"
  | Dmul -> "Dmul"
  | Dneg -> "Dneg"
  | Drem -> "Drem"
  | Dreturn -> "Dreturn"
  | Dstore _  -> "Dstore _"
  | Dstore_w _  -> "Dstore_w _"
  | Dstore_0 -> "Dstore_0"
  | Dstore_1 -> "Dstore_1"
  | Dstore_2 -> "Dstore_2"
  | Dstore_3 -> "Dstore_3"
  | Dsub -> "Dsub"
  | Dup -> "Dup"
  | Dup_x1 -> "Dup_x1"
  | Dup_x2 -> "Dup_x2"
  | Dup2 -> "Dup2"
  | Dup2_x1 -> "Dup2_x1"
  | Dup2_x2 -> "Dup2_x2"
  | F2d -> "F2d"
  | F2i -> "F2i"
  | F2l -> "F2l"
  | Fadd -> "Fadd"
  | Faload -> "Faload"
  | Fastore -> "Fastore"
  | Fcmpg -> "Fcmpg"
  | Fcmpl -> "Fcmpl"
  | Fconst_0 -> "Fconst_0"
  | Fconst_1 -> "Fconst_1"
  | Fconst_2 -> "Fconst_2"
  | Fdiv -> "Fdiv"
  | Fload _  -> "Fload _"
  | Fload_w _  -> "Fload_w _"
  | Fload_0 -> "Fload_0"
  | Fload_1 -> "Fload_1"
  | Fload_2 -> "Fload_2"
  | Fload_3 -> "Fload_3"
  | Fmul -> "Fmul"
  | Fneg -> "Fneg"
  | Frem -> "Frem"
  | Freturn -> "Freturn"
  | Fstore _  -> "Fstore _"
  | Fstore_w _  -> "Fstore_w _"
  | Fstore_0 -> "Fstore_0"
  | Fstore_1 -> "Fstore_1"
  | Fstore_2 -> "Fstore_2"
  | Fstore_3 -> "Fstore_3"
  | Fsub -> "Fsub"
  | Getfield _  -> "Getfield _"
  | Getstatic _  -> "Getstatic _"
  | Goto _  -> "Goto _"
  | Goto_w _  -> "Goto_w _"
  | I2b -> "I2b"
  | I2c -> "I2c"
  | I2d -> "I2d"
  | I2f -> "I2f"
  | I2l -> "I2l"
  | I2s -> "I2s"
  | Iadd -> "Iadd"
  | Iaload -> "Iaload"
  | Iand -> "Iand"
  | Iastore -> "Iastore"
  | Iconst_m1 -> "Iconst_m1"
  | Iconst_0 -> "Iconst_0"
  | Iconst_1 -> "Iconst_1"
  | Iconst_2 -> "Iconst_2"
  | Iconst_3 -> "Iconst_3"
  | Iconst_4 -> "Iconst_4"
  | Iconst_5 -> "Iconst_5"
  | Idiv -> "Idiv"
  | If_acmpeq _  -> "If_acmpeq _"
  | If_acmpne _  -> "If_acmpne _"
  | If_icmpeq _  -> "If_icmpeq _"
  | If_icmpne _  -> "If_icmpne _"
  | If_icmplt _  -> "If_icmplt _"
  | If_icmpge _  -> "If_icmpge _"
  | If_icmpgt _  -> "If_icmpgt _"
  | If_icmple _  -> "If_icmple _"
  | Ifeq _  -> "Ifeq _"
  | Ifne _  -> "Ifne _"
  | Iflt _  -> "Iflt _"
  | Ifge _  -> "Ifge _"
  | Ifgt _  -> "Ifgt _"
  | Ifle _  -> "Ifle _"
  | Ifnonnull _  -> "Ifnonnull _"
  | Ifnull _  -> "Ifnull _"
  | Iinc _  -> "Iinc _"
  | Iinc_w _  -> "Iinc_w _"
  | Iload _  -> "Iload _"
  | Iload_w _  -> "Iload_w _"
  | Iload_0 -> "Iload_0"
  | Iload_1 -> "Iload_1"
  | Iload_2 -> "Iload_2"
  | Iload_3 -> "Iload_3"
  | Imul -> "Imul"
  | Ineg -> "Ineg"
  | Instanceof _  -> "Instanceof _"
  | Invokeinterface _  -> "Invokeinterface _"
  | Invokespecial _  -> "Invokespecial _"
  | Invokestatic _  -> "Invokestatic _"
  | Invokevirtual _  -> "Invokevirtual _"
  | Ior -> "Ior"
  | Irem -> "Irem"
  | Ireturn -> "Ireturn"
  | Ishl -> "Ishl"
  | Ishr -> "Ishr"
  | Istore _  -> "Istore _"
  | Istore_w _  -> "Istore_w _"
  | Istore_0 -> "Istore_0"
  | Istore_1 -> "Istore_1"
  | Istore_2 -> "Istore_2"
  | Istore_3 -> "Istore_3"
  | Isub -> "Isub"
  | Iushr -> "Iushr"
  | Ixor -> "Ixor"
  | Jsr _  -> "Jsr _"
  | Jsr_w _  -> "Jsr_w _"
  | L2d -> "L2d"
  | L2f -> "L2f"
  | L2i -> "L2i"
  | Ladd -> "Ladd"
  | Laload -> "Laload"
  | Land -> "Land"
  | Lastore -> "Lastore"
  | Lcmp -> "Lcmp"
  | Lconst_0 -> "Lconst_0"
  | Lconst_1 -> "Lconst_1"
  | Ldc _  -> "Ldc _"
  | Ldc_w _  -> "Ldc_w _"
  | Ldc2_w _  -> "Ldc2_w _"
  | Ldiv -> "Ldiv"
  | Lload _  -> "Lload _"
  | Lload_w _  -> "Lload_w _"
  | Lload_0 -> "Lload_0"
  | Lload_1 -> "Lload_1"
  | Lload_2 -> "Lload_2"
  | Lload_3 -> "Lload_3"
  | Lmul -> "Lmul"
  | Lneg -> "Lneg"
  | Lookupswitch _  -> "Lookupswitch _"
  | Lor -> "Lor"
  | Lrem -> "Lrem"
  | Lreturn -> "Lreturn"
  | Lshl -> "Lshl"
  | Lshr -> "Lshr"
  | Lstore _  -> "Lstore _"
  | Lstore_w _  -> "Lstore_w _"
  | Lstore_0 -> "Lstore_0"
  | Lstore_1 -> "Lstore_1"
  | Lstore_2 -> "Lstore_2"
  | Lstore_3 -> "Lstore_3"
  | Lsub -> "Lsub"
  | Lushr -> "Lushr"
  | Lxor -> "Lxor"
  | Monitorenter -> "Monitorenter"
  | Monitorexit -> "Monitorexit"
  | Multianewarray _  -> "Multianewarray _"
  | New _  -> "New _"
  | Newarray _  -> "Newarray _"
  | Nop -> "Nop"
  | Pop -> "Pop"
  | Pop2 -> "Pop2"
  | Putfield _  -> "Putfield _"
  | Putstatic _  -> "Putstatic _"
  | Ret _  -> "Ret _"
  | Ret_w _  -> "Ret_w _"
  | Return -> "Return"
  | Saload -> "Saload"
  | Sastore -> "Sastore"
  | Sipush _  -> "Sipush _"
  | Swap -> "Swap"
  | Tableswitch _  -> "Tableswitch _"

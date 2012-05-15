open ExtArray

module LB = LowlevelBytecode
module CP = Constpool

type instr =
    (* A *)
  | Aaload
  | Aastore
  | Aconst_null
  | Aload of int
  | Anewarray of Jvmtype.jclass
  | Areturn
  | Arraylength
  | Astore of int
  | Athrow
      (* B *)
  | Baload
  | Bastore
      (* C *)
  | Caload
  | Castore
  | Checkcast of Jvmtype.jref_type
  | Classconst of Jvmtype.jref_type
      (* D *)
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
      (* F *)
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
      (* G *)
  | Getfield of Jvmtype.jclass * string * Jvmtype.jtype
  | Getstatic of Jvmtype.jclass * string * Jvmtype.jtype
  | Goto of int
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
      (* J *)
  | Jsr of int
      (* L *)
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
      (* M *)
  | Monitorenter
  | Monitorexit
  (*| Multianewarray of Constpool.index * int (** unsigned byte *) FIXME *)
      (* N *)
  | New of Jvmtype.jclass
  (*| Newarray of array_type FIXME *)
  | Nop
      (* P *)
  | Pop
  | Pop2
  | Putfield of Jvmtype.jclass * string * Jvmtype.jtype
  | Putstatic of Jvmtype.jclass * string * Jvmtype.jtype
      (* R *)
  | Ret of int
  | Return
      (* S *)
  | Saload
  | Sastore
  | Sconst of string
  | Swap
      (* T *)
  | Tableswitch of int * int32 * int list

exception TranslationError of string

let make_offset_table code =
  let table     = Array.make (Array.length code) (-1) in
  let trans_pos = ref 0 in
  let _         = Array.iteri (fun i op -> match op with None -> () | _ -> (table.(i) <- !trans_pos; incr trans_pos)) code in
    table

let of_lowlevel_bytecode cp instrs =
  let offset_table = make_offset_table instrs in
  let translate_instr offset instr = match instr with
    | LB.Aaload ->
	Aaload
    | LB.Aastore ->
	Aastore
    | LB.Aconst_null ->
	Aconst_null
    | LB.Aload i
    | LB.Aload_w i ->
	Aload i
    | LB.Aload_0 ->
	Aload 0
    | LB.Aload_1 ->
	Aload 1
    | LB.Aload_2 ->
	Aload 2
    | LB.Aload_3 ->
	Aload 3
    | LB.Anewarray idx ->
	failwith "not yet implemented: anewarray"
    | LB.Areturn ->
	Areturn
    | LB.Arraylength ->
	Arraylength
    | LB.Astore i
    | LB.Astore_w i ->
	Astore i
    | LB.Astore_0 ->
	Astore 0
    | LB.Astore_1 ->
	Astore 1
    | LB.Astore_2 ->
	Astore 2
    | LB.Astore_3 ->
	Astore 3
    | LB.Athrow ->
	Athrow
	  (* B *)
    | LB.Baload ->
	Baload
    | LB.Bastore ->
	Bastore
    | LB.Bipush i ->
	Iconst (Int32.of_int i)
    | LB.Caload ->
	Caload
    | LB.Castore ->
	Castore
    | LB.Checkcast idx ->
	Checkcast (CP.lookup_class cp idx)
    | LB.D2f ->
	D2f
    | LB.D2i ->
	D2i
    | LB.D2l ->
	D2l
    | LB.Dadd ->
	Dadd
    | LB.Daload ->
	Daload
    | LB.Dastore ->
	Dastore
    | LB.Dcmpg ->
	Dcmpg
    | LB.Dcmpl ->
	Dcmpl
    | LB.Dconst_0 ->
	Dconst 0.0
    | LB.Dconst_1 ->
	Dconst 1.0
    | LB.Ddiv ->
	Ddiv
    | LB.Dload i
    | LB.Dload_w i ->
	Dload i
    | LB.Dload_0 ->
	Dload 0
    | LB.Dload_1 ->
	Dload 1
    | LB.Dload_2 ->
	Dload 2
    | LB.Dload_3 ->
	Dload 3
    | LB.Dmul ->
	Dmul
    | LB.Dneg ->
	Dneg
    | LB.Drem ->
	Drem
    | LB.Dreturn ->
	Dreturn
    | LB.Dstore i
    | LB.Dstore_w i ->
	Dstore i
    | LB.Dstore_0 ->
	Dstore 0
    | LB.Dstore_1 ->
	Dstore 1
    | LB.Dstore_2 ->
	Dstore 2
    | LB.Dstore_3 ->
	Dstore 3
    | LB.Dsub ->
	Dsub
    | LB.Dup ->
	Dup
    | LB.Dup_x1 ->
	Dup_x1
    | LB.Dup_x2 ->
	Dup_x2
    | LB.Dup2 -> 
	Dup2
    | LB.Dup2_x1 ->
	Dup2_x1
    | LB.Dup2_x2 ->
	Dup2_x2
	  (* F *)
    | LB.F2d ->
	F2d
    | LB.F2i ->
	F2i
    | LB.F2l ->
	F2l
    | LB.Fadd ->
	Fadd
    | LB.Faload ->
	Faload
    | LB.Fastore ->
	Fastore
    | LB.Fcmpg ->
	Fcmpg
    | LB.Fcmpl ->
	Fcmpl
    | LB.Fconst_0 ->
	Fconst JFloat.zero
    | LB.Fconst_1 ->
	Fconst JFloat.one
    | LB.Fconst_2 ->
	Fconst JFloat.two
    | LB.Fdiv ->
	Fdiv
    | LB.Fload i
    | LB.Fload_w i ->
	Fload i
    | LB.Fload_0 ->
	Fload 0
    | LB.Fload_1 ->
	Fload 1
    | LB.Fload_2 ->
	Fload 2
    | LB.Fload_3 ->
	Fload 3
    | LB.Fmul ->
	Fmul
    | LB.Fneg ->
	Fneg
    | LB.Frem ->
	Frem
    | LB.Freturn ->
	Freturn
    | LB.Fstore i
    | LB.Fstore_w i ->
	Fstore i
    | LB.Fstore_0 ->
	Fstore 0
    | LB.Fstore_1 ->
	Fstore 1
    | LB.Fstore_2 ->
	Fstore 2
    | LB.Fstore_3 ->
	Fstore 3
    | LB.Fsub ->
	Fsub
	  (* G *)
    | LB.Getfield idx ->
	let clsnm, fnm, fty = CP.lookup_fieldref cp idx in
	  Getfield (clsnm, fnm, fty)
    | LB.Getstatic idx ->
	let clsnm, fnm, fty = CP.lookup_fieldref cp idx in
	  Getfield (clsnm, fnm, fty)
    | LB.Goto jump_offset ->
	Goto (offset_table.(offset + jump_offset))
    | LB.Goto_w jump_offset ->
	Goto (offset_table.(offset + Int32.to_int jump_offset))
	  (* I *)
    | LB.I2b ->
	I2b
    | LB.I2c ->
	I2c
    | LB.I2d ->
	I2d
    | LB.I2f ->
	I2f
    | LB.I2l ->
	I2l
    | LB.I2s ->
	I2s
    | LB.Iadd ->
	Iadd
    | LB.Iaload ->
	Iaload
    | LB.Iand ->
	Iand
    | LB.Iastore ->
	Iastore
    | LB.Iconst_m1 ->
	Iconst (-1l)
    | LB.Iconst_0 ->
	Iconst 0l
    | LB.Iconst_1 ->
	Iconst 1l
    | LB.Iconst_2 ->
	Iconst 2l
    | LB.Iconst_3 ->
	Iconst 3l
    | LB.Iconst_4 ->
	Iconst 4l
    | LB.Iconst_5 ->
	Iconst 5l
    | LB.Idiv ->
	Idiv
    | LB.If_acmpeq jump_offset ->
	If_acmpeq (offset_table.(offset + jump_offset))
    | LB.If_acmpne jump_offset ->
	If_acmpne (offset_table.(offset + jump_offset))
    | LB.If_icmpeq jump_offset ->
	If_icmpeq (offset_table.(offset + jump_offset))
    | LB.If_icmpne jump_offset ->
	If_icmpne (offset_table.(offset + jump_offset))
    | LB.If_icmple jump_offset ->
	If_icmple (offset_table.(offset + jump_offset))
    | LB.If_icmplt jump_offset ->
	If_icmplt (offset_table.(offset + jump_offset))
    | LB.If_icmpge jump_offset ->
	If_icmpge (offset_table.(offset + jump_offset))
    | LB.If_icmpgt jump_offset ->
	If_icmpgt (offset_table.(offset + jump_offset))
    | LB.Ifeq jump_offset ->
	Ifeq (offset_table.(offset + jump_offset))
    | LB.Ifne jump_offset ->
	Ifne (offset_table.(offset + jump_offset))
    | LB.Ifle jump_offset ->
	Ifle (offset_table.(offset + jump_offset))
    | LB.Iflt jump_offset ->
	Iflt (offset_table.(offset + jump_offset))
    | LB.Ifge jump_offset ->
	Ifge (offset_table.(offset + jump_offset))
    | LB.Ifgt jump_offset ->
	Ifgt (offset_table.(offset + jump_offset))
    | LB.Ifnull jump_offset ->
	Ifnull (offset_table.(offset + jump_offset))
    | LB.Ifnonnull jump_offset ->
	Ifnonnull (offset_table.(offset + jump_offset))
    | LB.Iinc (x,y)
    | LB.Iinc_w (x,y) ->
	Iinc (x,y)
    | LB.Iload i
    | LB.Iload_w i ->
	Iload i
    | LB.Iload_0 ->
	Iload 0
    | LB.Iload_1 ->
	Iload 1
    | LB.Iload_2 ->
	Iload 2
    | LB.Iload_3 ->
	Iload 3
    | LB.Imul ->
	Imul
    | LB.Ineg ->
	Ineg
    | LB.Instanceof idx ->
	Instanceof (CP.lookup_class_notarray cp idx)
    | LB.Invokeinterface (idx,_) ->
	let cnm,mnm,msig = CP.lookup_imethodref cp idx in Invokeinterface (cnm, mnm, msig)
    | LB.Invokespecial idx ->
	let cnm,mnm,msig = CP.lookup_methodref cp idx in Invokespecial (cnm, mnm, msig)
    | LB.Invokestatic idx ->
	let cnm,mnm,msig = CP.lookup_methodref cp idx in Invokestatic (cnm, mnm, msig)
    | LB.Invokevirtual idx ->
	let cnm,mnm,msig = CP.lookup_methodref cp idx in Invokevirtual (cnm, mnm, msig)
    | LB.Ior ->
	Ior
    | LB.Irem ->
	Irem
    | LB.Ireturn ->
	Ireturn
    | LB.Ishl ->
	Ishl
    | LB.Ishr ->
	Ishr
    | LB.Istore i
    | LB.Istore_w i ->
	Istore i
    | LB.Istore_0 ->
	Istore 0
    | LB.Istore_1 ->
	Istore 1
    | LB.Istore_2 ->
	Istore 2
    | LB.Istore_3 ->
	Istore 3
    | LB.Isub ->
	Isub
    | LB.Iushr ->
	Iushr
    | LB.Ixor ->
	Ixor
	  (* J *)
    | LB.Jsr jump_offset ->
	Jsr (offset_table.(jump_offset + offset))
    | LB.Jsr_w jump_offset ->
	Jsr (offset_table.(offset + Int32.to_int jump_offset))
	  (* L *)
    | LB.L2d ->
	L2d
    | LB.L2f ->
	L2f
    | LB.L2i ->
	L2i
    | LB.Ladd ->
	Ladd
    | LB.Laload ->
	Laload
    | LB.Land ->
	Land
    | LB.Lastore ->
	Lastore
    | LB.Lcmp ->
	Lcmp
    | LB.Lconst_0 ->
	Lconst 0L
    | LB.Lconst_1 ->
	Lconst 1L
    | LB.Ldc idx
    | LB.Ldc_w idx ->
	(match CP.lookup cp idx with
	   | CP.CPstring i -> Sconst (CP.lookup_utf8 cp i)
	   | CP.CPint i    -> Iconst i
	   | CP.CPfloat f  -> Fconst f
	   | CP.CPclass _  -> Classconst (CP.lookup_class cp idx)
	   | _             -> raise (TranslationError ("Incorrect constant for ldc")))
    | LB.Ldc2_w idx ->
	(match CP.lookup cp idx with
	   | CP.CPdouble d -> Dconst d
	   | CP.CPlong l   -> Lconst l
	   | _             -> raise (TranslationError ("Incorrect constant for ldc2")))
    | LB.Ldiv ->
	Ldiv
    | LB.Lload i
    | LB.Lload_w i ->
	Lload i
    | LB.Lload_0 ->
	Lload 0
    | LB.Lload_1 ->
	Lload 1
    | LB.Lload_2 ->
	Lload 2
    | LB.Lload_3 ->
	Lload 3
    | LB.Lmul ->
	Lmul
    | LB.Lneg ->
	Lneg
    | LB.Lookupswitch (default, pairs) ->
	Lookupswitch (offset_table.(offset + Int32.to_int default),
		      List.map (fun (n, jump_offset) -> (n, offset_table.(offset + Int32.to_int jump_offset))) pairs)
    | LB.Lor ->
	Lor
    | LB.Lrem ->
	Lrem
    | LB.Lreturn ->
	Lreturn
    | LB.Lshl ->
	Lshl
    | LB.Lshr ->
	Lshr
    | LB.Lstore i
    | LB.Lstore_w i ->
	Lstore i
    | LB.Lstore_0 ->
	Lstore 0
    | LB.Lstore_1 ->
	Lstore 1
    | LB.Lstore_2 ->
	Lstore 2
    | LB.Lstore_3 ->
	Lstore 3
    | LB.Lsub ->
	Lsub
    | LB.Lushr ->
	Lushr
    | LB.Lxor ->
	Lxor

    (* M *)
    | LB.Monitorenter ->
	Monitorenter
    | LB.Monitorexit ->
	Monitorexit
    | LB.Multianewarray (idx, dim) ->
	failwith "not yet implemented: multianewarray"
    
    (* N *)
    | LB.New idx ->
	New (CP.lookup_class_notarray cp idx)
    | LB.Newarray t ->
	failwith "not yet implemented: newarray"
    | LB.Nop ->
	Nop

    (* P *)
    | LB.Pop ->
	Pop
    | LB.Pop2 ->
	Pop2
    | LB.Putfield idx ->
	let cnm,fnm,fty = CP.lookup_fieldref cp idx in Putfield (cnm,fnm,fty)
    | LB.Putstatic idx ->
	let cnm,fnm,fty = CP.lookup_fieldref cp idx in Putstatic (cnm,fnm,fty)

    (* R *)
    | LB.Ret i
    | LB.Ret_w i                 ->
	Ret i
    | LB.Return                  ->
	Return

    (* S *)
    | LB.Saload                  ->
	Saload
    | LB.Sastore                 ->
	Sastore
    | LB.Sipush i                ->
	Iconst (Int32.of_int i)
    | LB.Swap                    ->
	Swap
    
    (* T *)
    | LB.Tableswitch (default,low,l) ->
	Tableswitch (offset_table.(offset + Int32.to_int default),
		     low,
		     List.map (fun jo -> offset_table.(offset + Int32.to_int jo)) l)
  in
  let rec loop offset acc =
    if offset = Array.length instrs then
      acc
    else
      match instrs.(offset) with
	| None -> loop (offset+1) acc
	| Some instr -> loop (offset+1) (translate_instr offset instr::acc)
  in
  let new_instrs = Array.of_list (loop 0 []) in
    Array.rev_in_place new_instrs;
    new_instrs

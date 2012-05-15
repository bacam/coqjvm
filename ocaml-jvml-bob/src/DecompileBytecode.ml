module B  = Bytecode
module LB = LowlevelBytecode
module CP = Constpool
module JT = Jvmtype

exception DecompileBytecodeError of string

type label_map_builder =
    { label_gen : Label.labels
    ; label_map : (int, Label.label) Hashtbl.t
    }

let create_label_map_builder () =
  { label_gen = Label.label_generator ()
  ; label_map = Hashtbl.create 10
  }

let decompile_offset label_map_builder offset = 
  try Hashtbl.find label_map_builder.label_map offset
  with Not_found ->
    let l = Label.new_label label_map_builder.label_gen in
    let _ = Hashtbl.add label_map_builder.label_map offset l in
      l

let find_label label_map_builder offset =
  try Some (Hashtbl.find label_map_builder.label_map offset)
  with Not_found -> None

let gather_labels label_map_builder instrs =
  let gather_label offset instr = match instr with
    | Some (LB.Lookupswitch (default, pairs)) ->
	ignore (decompile_offset label_map_builder (offset + Int32.to_int default)); (* FIXME: overflow? *)
	List.iter (fun (_,jo) -> ignore (decompile_offset label_map_builder (offset + Int32.to_int jo))) pairs
    | Some (LB.Goto jump_offset) 
    | Some (LB.If_acmpeq jump_offset)
    | Some (LB.If_acmpne jump_offset)
    | Some (LB.If_icmpeq jump_offset)
    | Some (LB.If_icmpne jump_offset)
    | Some (LB.If_icmplt jump_offset)
    | Some (LB.If_icmpge jump_offset)
    | Some (LB.If_icmpgt jump_offset)
    | Some (LB.If_icmple jump_offset)
    | Some (LB.Ifeq jump_offset)
    | Some (LB.Ifne jump_offset)
    | Some (LB.Iflt jump_offset)
    | Some (LB.Ifge jump_offset)
    | Some (LB.Ifgt jump_offset)
    | Some (LB.Ifle jump_offset)
    | Some (LB.Ifnonnull jump_offset)
    | Some (LB.Ifnull jump_offset)
    | Some (LB.Jsr jump_offset) ->
	let offset' = offset + jump_offset in
	let _       = decompile_offset label_map_builder offset' in
	  ()
    | Some (LB.Jsr_w jump_offset)
    | Some (LB.Goto_w jump_offset) ->
	let jump_offset = Int32.to_int jump_offset in (* FIXME: no need to check for oveflow? *)
	let offset'     = offset + jump_offset in
	let _           = decompile_offset label_map_builder offset' in
	  ()
    | Some (LB.Tableswitch (default,_,l)) ->
	ignore (decompile_offset label_map_builder (offset + Int32.to_int default));
	List.iter (fun jo -> ignore (decompile_offset label_map_builder (offset + Int32.to_int jo))) l
    | _ ->
	()
  in
    Array.iteri gather_label instrs

let decompile_bytecode pool label_map_builder instrs =
  let decompile_instr offset instr = match instr with
      (* A *)
    | LB.Aaload        -> B.Jaaload
    | LB.Aastore       -> B.Jaastore
    | LB.Aconst_null   -> B.Jaconst_null
    | LB.Aload i
    | LB.Aload_w i     -> B.Jaload i
    | LB.Aload_0       -> B.Jaload 0
    | LB.Aload_1       -> B.Jaload 1
    | LB.Aload_2       -> B.Jaload 2
    | LB.Aload_3       -> B.Jaload 3
    | LB.Anewarray idx ->
	let element_type = CP.lookup_class pool idx in
	  B.Jnewarray (JT.TRef element_type, 1)
    | LB.Areturn       -> B.Jreturn
    | LB.Arraylength   -> B.Jarraylength
    | LB.Astore i
    | LB.Astore_w i    -> B.Jastore i
    | LB.Astore_0      -> B.Jastore 0
    | LB.Astore_1      -> B.Jastore 1
    | LB.Astore_2      -> B.Jastore 2
    | LB.Astore_3      -> B.Jastore 3
    | LB.Athrow        -> B.Jathrow

    (* B *)
    | LB.Baload        -> B.Jbaload
    | LB.Bastore       -> B.Jbastore
    | LB.Bipush i      -> B.Jiconst (Int32.of_int i)

    (* C *)
    | LB.Caload        -> B.Jcaload
    | LB.Castore       -> B.Jcastore
    | LB.Checkcast idx -> B.Jcheckcast (CP.lookup_class pool idx)

    (* D *)
    | LB.D2f           -> B.Jd2f
    | LB.D2i           -> B.Jd2i
    | LB.D2l           -> B.Jd2l
    | LB.Dadd          -> B.Jdadd
    | LB.Daload        -> B.Jdaload
    | LB.Dastore       -> B.Jdastore
    | LB.Dcmpg         -> B.Jdcmpg
    | LB.Dcmpl         -> B.Jdcmpl
    | LB.Dconst_0      -> B.Jdconst 0.0
    | LB.Dconst_1      -> B.Jdconst 1.0
    | LB.Ddiv          -> B.Jddiv
    | LB.Dload i
    | LB.Dload_w i     -> B.Jdload i
    | LB.Dload_0       -> B.Jdload 0
    | LB.Dload_1       -> B.Jdload 1
    | LB.Dload_2       -> B.Jdload 2
    | LB.Dload_3       -> B.Jdload 3
    | LB.Dmul          -> B.Jdmul
    | LB.Dneg          -> B.Jdneg
    | LB.Drem          -> B.Jdrem
    | LB.Dreturn       -> B.Jreturn
    | LB.Dstore i
    | LB.Dstore_w i    -> B.Jdstore i
    | LB.Dstore_0      -> B.Jdstore 0
    | LB.Dstore_1      -> B.Jdstore 1
    | LB.Dstore_2      -> B.Jdstore 2
    | LB.Dstore_3      -> B.Jdstore 3
    | LB.Dsub          -> B.Jdsub
    | LB.Dup           -> B.Jdup
    | LB.Dup_x1        -> B.Jdup_x1
    | LB.Dup_x2        -> B.Jdup_x2
    | LB.Dup2          -> B.Jdup2
    | LB.Dup2_x1       -> B.Jdup2_x1
    | LB.Dup2_x2       -> B.Jdup2_x2

    (* F *)
    | LB.F2d           -> B.Jf2d
    | LB.F2i           -> B.Jf2i
    | LB.F2l           -> B.Jf2l
    | LB.Fadd          -> B.Jfadd
    | LB.Faload        -> B.Jfaload
    | LB.Fastore       -> B.Jfastore
    | LB.Fcmpg         -> B.Jfcmpg
    | LB.Fcmpl         -> B.Jfcmpl
    | LB.Fconst_0      -> B.Jfconst JFloat.zero
    | LB.Fconst_1      -> B.Jfconst JFloat.one
    | LB.Fconst_2      -> B.Jfconst JFloat.two
    | LB.Fdiv          -> B.Jfdiv
    | LB.Fload i
    | LB.Fload_w i     -> B.Jfload i
    | LB.Fload_0       -> B.Jfload 0
    | LB.Fload_1       -> B.Jfload 1
    | LB.Fload_2       -> B.Jfload 2
    | LB.Fload_3       -> B.Jfload 3
    | LB.Fmul          -> B.Jfmul
    | LB.Fneg          -> B.Jfneg
    | LB.Frem          -> B.Jfrem
    | LB.Freturn       -> B.Jreturn
    | LB.Fstore i
    | LB.Fstore_w i    -> B.Jfstore i
    | LB.Fstore_0      -> B.Jfstore 0
    | LB.Fstore_1      -> B.Jfstore 1
    | LB.Fstore_2      -> B.Jfstore 2
    | LB.Fstore_3      -> B.Jfstore 3
    | LB.Fsub          -> B.Jfsub

    (* G *)
    | LB.Getfield idx  -> 
	let cnm, fnm, ftype = CP.lookup_fieldref pool idx in B.Jgetfield (cnm, fnm, ftype)
    | LB.Getstatic idx ->
	let cnm, fnm, ftype = CP.lookup_fieldref pool idx in B.Jgetstatic (cnm, fnm, ftype)
    | LB.Goto jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: Label not there for goto"
	  | Some label -> B.Jgoto label)
    | LB.Goto_w jump_offset ->
	(match find_label label_map_builder (offset + Int32.to_int jump_offset) with (* FIXME: overflow? *)
	  | None       -> failwith "Internal bug: Label not there for goto_w"
	  | Some label -> B.Jgoto label)

    (* I *)
    | LB.I2b                 -> B.Ji2b
    | LB.I2c                 -> B.Ji2c
    | LB.I2d                 -> B.Ji2d
    | LB.I2f                 -> B.Ji2f
    | LB.I2l                 -> B.Ji2l
    | LB.I2s                 -> B.Ji2s
    | LB.Iadd                -> B.Jiadd
    | LB.Iaload              -> B.Jiaload
    | LB.Iand                -> B.Jiand
    | LB.Iastore             -> B.Jiastore
    | LB.Iconst_m1           -> B.Jiconst (-1l)
    | LB.Iconst_0            -> B.Jiconst 0l
    | LB.Iconst_1            -> B.Jiconst 1l
    | LB.Iconst_2            -> B.Jiconst 2l
    | LB.Iconst_3            -> B.Jiconst 3l
    | LB.Iconst_4            -> B.Jiconst 4l
    | LB.Iconst_5            -> B.Jiconst 5l
    | LB.Idiv                -> B.Jidiv
    | LB.If_acmpeq jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for if_acmpeq"
	  | Some label -> B.Jif_acmpeq label)
    | LB.If_acmpne jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for if_acmpne"
	  | Some label -> B.Jif_acmpne label)
    | LB.If_icmpeq jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for if_icmpeq"
	  | Some label -> B.Jif_icmpeq label)
    | LB.If_icmpne jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for if_icmpne"
	  | Some label -> B.Jif_icmpne label)
    | LB.If_icmplt jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for if_icmplt"
	  | Some label -> B.Jif_icmplt label)
    | LB.If_icmple jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for if_icmple"
	  | Some label -> B.Jif_icmple label)
    | LB.If_icmpgt jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for if_icmpgt"
	  | Some label -> B.Jif_icmpgt label)
    | LB.If_icmpge jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for if_icmpge"
	  | Some label -> B.Jif_icmpge label)
    | LB.Ifeq jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for ifeq"
	  | Some label -> B.Jifeq label)
    | LB.Ifne jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for ifne"
	  | Some label -> B.Jifne label)
    | LB.Iflt jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for iflt"
	  | Some label -> B.Jiflt label)
    | LB.Ifle jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for ifle"
	  | Some label -> B.Jifle label)
    | LB.Ifgt jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for ifgt"
	  | Some label -> B.Jifgt label)
    | LB.Ifge jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for ifge"
	  | Some label -> B.Jifge label)
    | LB.Ifnull jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for ifnull"
	  | Some label -> B.Jifnull label)
    | LB.Ifnonnull jump_offset ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: label not found for ifnonnull"
	  | Some label -> B.Jifnonnull label)
    | LB.Iinc (i, o)
    | LB.Iinc_w (i,o)            -> B.Jiinc (i, o)
    | LB.Iload i
    | LB.Iload_w i               -> B.Jiload i
    | LB.Iload_0                 -> B.Jiload 0
    | LB.Iload_1                 -> B.Jiload 1
    | LB.Iload_2                 -> B.Jiload 2
    | LB.Iload_3                 -> B.Jiload 3
    | LB.Imul                    -> B.Jimul
    | LB.Ineg                    -> B.Jineg
    | LB.Instanceof idx          -> let cnm = CP.lookup_class pool idx in B.Jinstanceof cnm
    | LB.Invokeinterface (idx,_) -> let cnm,mnm,msig = CP.lookup_imethodref pool idx in B.Jinvokeinterface (cnm, mnm, msig)
    | LB.Invokespecial idx       -> let cnm,mnm,msig = CP.lookup_methodref pool idx in B.Jinvokespecial (cnm, mnm, msig)
    | LB.Invokestatic idx        -> let cnm,mnm,msig = CP.lookup_methodref pool idx in B.Jinvokestatic (cnm, mnm, msig)
    | LB.Invokevirtual idx       -> let cnm,mnm,msig = CP.lookup_methodref pool idx in B.Jinvokevirtual (cnm, mnm, msig)
    | LB.Ior                     -> B.Jior
    | LB.Irem                    -> B.Jirem
    | LB.Ireturn                 -> B.Jreturn
    | LB.Ishl                    -> B.Jishl
    | LB.Ishr                    -> B.Jishr
    | LB.Istore i
    | LB.Istore_w i              -> B.Jistore i
    | LB.Istore_0                -> B.Jistore 0
    | LB.Istore_1                -> B.Jistore 1
    | LB.Istore_2                -> B.Jistore 2
    | LB.Istore_3                -> B.Jistore 3
    | LB.Isub                    -> B.Jisub
    | LB.Iushr                   -> B.Jiushr
    | LB.Ixor                    -> B.Jixor

    (* J *)
    | LB.Jsr jump_offset         ->
	(match find_label label_map_builder (offset + jump_offset) with
	  | None       -> failwith "Internal bug: Label not there for jsr"
	  | Some label -> B.Jjsr label)
    | LB.Jsr_w jump_offset ->
	(match find_label label_map_builder (offset + Int32.to_int jump_offset) with (* FIXME: overflow? *)
	  | None       -> failwith "Internal bug: Label not there for jsr_w"
	  | Some label -> B.Jjsr label)

    (* L *)
    | LB.L2d                     -> B.Jl2d
    | LB.L2f                     -> B.Jl2f
    | LB.L2i                     -> B.Jl2i
    | LB.Ladd                    -> B.Jladd
    | LB.Laload                  -> B.Jlaload
    | LB.Land                    -> B.Jland
    | LB.Lastore                 -> B.Jlastore
    | LB.Lcmp                    -> B.Jlcmp
    | LB.Lconst_0                -> B.Jlconst 0L
    | LB.Lconst_1                -> B.Jlconst 1L
    | LB.Ldc idx
    | LB.Ldc_w idx               ->
	(match CP.lookup pool idx with
	   | CP.CPstring i -> B.Jsconst (CP.lookup_utf8 pool i)
	   | CP.CPint i    -> B.Jiconst i
	   | CP.CPfloat f  -> B.Jfconst f
	   | CP.CPclass _  -> B.Jclassconst (CP.lookup_class pool idx)
	   | _             -> raise (DecompileBytecodeError ("Incorrect constant for ldc")))
    | LB.Ldc2_w idx              ->
	(match CP.lookup pool idx with
	   | CP.CPdouble d -> B.Jdconst d
	   | CP.CPlong l   -> B.Jlconst l
	   | _             -> raise (DecompileBytecodeError ("Incorrect constant for ldc2")))
    | LB.Ldiv                    -> B.Jldiv
    | LB.Lload i
    | LB.Lload_w i               -> B.Jlload i
    | LB.Lload_0                 -> B.Jlload 0
    | LB.Lload_1                 -> B.Jlload 1
    | LB.Lload_2                 -> B.Jlload 2
    | LB.Lload_3                 -> B.Jlload 3
    | LB.Lmul                    -> B.Jlmul
    | LB.Lneg                    -> B.Jlneg
    | LB.Lookupswitch (default, pairs) ->
	(match find_label label_map_builder (offset + Int32.to_int default) with
	   | None -> failwith "Internal bug: Label not there for lookupswitch"
	   | Some default ->
	       let decompile_pair (n,jo) = (match find_label label_map_builder (offset + Int32.to_int jo) with
					      | None -> failwith "Internal bug: Label not there for lookupswitch"
					      | Some label -> (n,label)) in
	       let pairs = List.map decompile_pair pairs in
		 B.Jlookupswitch (default, pairs))
    | LB.Lor                     -> B.Jlor
    | LB.Lrem                    -> B.Jlrem
    | LB.Lreturn                 -> B.Jreturn
    | LB.Lshl                    -> B.Jlshl
    | LB.Lshr                    -> B.Jlshr
    | LB.Lstore i
    | LB.Lstore_w i              -> B.Jlstore i
    | LB.Lstore_0                -> B.Jlstore 0
    | LB.Lstore_1                -> B.Jlstore 1
    | LB.Lstore_2                -> B.Jlstore 2
    | LB.Lstore_3                -> B.Jlstore 3
    | LB.Lsub                    -> B.Jlsub
    | LB.Lushr                   -> B.Jlushr
    | LB.Lxor                    -> B.Jlxor

    (* M *)
    | LB.Monitorenter            -> B.Jmonitorenter
    | LB.Monitorexit             -> B.Jmonitorexit
    | LB.Multianewarray (idx,dim)->
	let cnm = CP.lookup_class pool idx in
	let rec remove_dimensions n t = if n = 0 then t else match t with
	  | JT.TRef (JT.TArray t) -> remove_dimensions (n-1) t
	  | _                     -> raise (DecompileBytecodeError "Incorrect dimensions in multianewarray")
	in
	let t = remove_dimensions dim (JT.TRef cnm) in
	  B.Jnewarray (t, dim)

    (* N *)
    | LB.New idx                 ->
	(match CP.lookup_class pool idx with
	   | JT.TObject cnm -> B.Jnew cnm
	   | _              -> raise (DecompileBytecodeError "Array types not allowed in new instruction")) (* FIXME: technically, the spec allows arrays, but it fails elsewhere: need to check what JVM does *)
    | LB.Newarray t              ->
	let t = (match t with
		   | LB.Array_boolean  -> JT.TBoolean
		   | LB.Array_char     -> JT.TChar
		   | LB.Array_float    -> JT.TFloat
		   | LB.Array_double   -> JT.TDouble
		   | LB.Array_byte     -> JT.TByte
		   | LB.Array_int      -> JT.TInt
		   | LB.Array_short    -> JT.TShort
		   | LB.Array_long     -> JT.TLong)
	in
	  B.Jnewarray (t, 1)
    | LB.Nop                     -> B.Jnop
    
    (* P *)
    | LB.Pop                     -> B.Jpop
    | LB.Pop2                    -> B.Jpop2
    | LB.Putfield idx            -> let cnm,fnm,fty = CP.lookup_fieldref pool idx in B.Jputfield (cnm,fnm,fty)
    | LB.Putstatic idx           -> let cnm,fnm,fty = CP.lookup_fieldref pool idx in B.Jputstatic (cnm,fnm,fty)

    (* R *)
    | LB.Ret i
    | LB.Ret_w i                 -> B.Jret i
    | LB.Return                  -> B.Jreturn

    (* S *)
    | LB.Saload                  -> B.Jsaload
    | LB.Sastore                 -> B.Jsastore
    | LB.Sipush i                -> B.Jiconst (Int32.of_int i)
    | LB.Swap                    -> B.Jswap
    
    (* T *)
    | LB.Tableswitch (default,low,l) ->
	let decompile_jump_offset jo = (match find_label label_map_builder (offset + Int32.to_int jo) with
					  | None       -> failwith "Internal bug: label not present for tableswitch"
					  | Some label -> label) in
	  B.Jtableswitch (decompile_jump_offset default,
			  low,
			  List.map decompile_jump_offset l)

  in
  let rec loop offset hlinstrs =
    if offset < 0 then
      hlinstrs
    else if offset = Array.length instrs then
      let hlinstrs = (match find_label label_map_builder offset with
                       | None       -> hlinstrs
		       | Some label -> B.Jlabel (label, ())::hlinstrs) in
	loop (offset-1) hlinstrs
    else
      let hlinstrs = (match instrs.(offset) with
	               | None       -> hlinstrs
		       | Some instr -> decompile_instr offset instr::hlinstrs) in
      let hlinstrs = (match find_label label_map_builder offset with
                       | None       -> hlinstrs
		       | Some label -> B.Jlabel (label, ())::hlinstrs) in
	loop (offset-1) hlinstrs
  in
    gather_labels label_map_builder instrs;
    loop (Array.length instrs) [];

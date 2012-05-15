(* plan: take a first pass through the hl-instruction list, guessing
   sizes for each of the instructions to build up an offset table
   mapping locations in the hl-list to ones in the ll-array. Then do a
   second pass, writing out instructions and using the lookup table.
   should also be able to work out when to make some gotos smaller *)

module B = Bytecode
module LB = LowlevelBytecode
module CP = Constpool

exception CompileBytecodeError of string

let is_ui8 i = 0 <= i && i <= 255

let is_i8 i = -128l <= i && i <= 127l

let is_i16 i = -0x8000l <= i && i <= 0x7fffl

let is_ui16 i = 0 <= i && i <= 0xffff

let add_constants_to_pool builder instrs =
  (* we don't need to add long and double constants here because they will
     always need a ldc2_w instruction *)
  let process_instruction i = match i with
    | B.Jclassconst ref_type           -> let _ = CP.add_class builder ref_type in ()
    | B.Jsconst s                      -> let _ = CP.add_string builder s in ()
    | B.Jfconst f when f <> JFloat.one && f <> JFloat.zero && f <> JFloat.two
                                       -> let _ = CP.add_float builder f in ()
    | B.Jiconst i when not (is_i16 i)  -> let _ = CP.add_int builder i in ()
    | _                                -> ()
  in
    List.iter process_instruction instrs

(* this function computes the padding required by the lookupswitch and
   tableswitch instructions *)
let padding offset = (4 - ((offset + 1) mod 4)) mod 4

let create_label_table builder instrs =
  let mapping = Hashtbl.create 10 in
  let changed = ref false in

  let ldc_length index_opt = match index_opt with
    | None       -> raise (CompileBytecodeError "create_label_table: should already have constants in constant pool")
    | Some index -> if CP.index_to_int index <= 255 then 2 else 3
  in

  let instruction_length instr offset = match instr with
    | B.Jlabel (label, _) ->
	if Hashtbl.mem mapping label && Hashtbl.find mapping label = offset then
	  0
	else
	  (Hashtbl.replace mapping label offset;
	   changed := true;
	   0)
    | B.Jaaload | B.Jaastore | B.Jaconst_null | B.Jarraylength
    | B.Jathrow | B.Jbaload | B.Jbastore | B.Jcaload | B.Jcastore
    | B.Jd2f | B.Jd2i | B.Jd2l | B.Jdadd | B.Jdaload 
    | B.Jdastore | B.Jdcmpg | B.Jdcmpl | B.Jddiv | B.Jdmul
    | B.Jdneg | B.Jdrem | B.Jdsub | B.Jdup | B.Jdup_x1 | B.Jdup_x2
    | B.Jdup2 | B.Jdup2_x1 | B.Jdup2_x2 | B.Jf2d | B.Jf2i | B.Jf2l
    | B.Jfadd | B.Jfaload | B.Jfastore | B.Jfcmpg | B.Jfcmpl | B.Jfdiv
    | B.Jfmul | B.Jfneg | B.Jfrem | B.Jfsub | B.Ji2b | B.Ji2c | B.Ji2d
    | B.Ji2f | B.Ji2l | B.Ji2s | B.Jiadd | B.Jiaload | B.Jiand
    | B.Jiastore | B.Jidiv | B.Jimul | B.Jineg | B.Jior | B.Jirem
    | B.Jishl | B.Jishr | B.Jisub | B.Jiushr | B.Jixor | B.Jl2d | B.Jl2f
    | B.Jl2i | B.Jladd | B.Jlaload | B.Jland | B.Jlastore | B.Jlcmp
    | B.Jldiv | B.Jlmul | B.Jlneg | B.Jlor | B.Jlrem | B.Jlshl
    | B.Jlshr | B.Jlsub | B.Jlushr | B.Jlxor | B.Jmonitorenter
    | B.Jmonitorexit | B.Jnop | B.Jpop| B.Jpop2 | B.Jreturn | B.Jsaload
    | B.Jsastore | B.Jswap ->
	1
    | B.Jclassconst ref_type ->
	ldc_length (CP.find_class builder ref_type)
    | B.Jsconst s -> ldc_length (CP.find_string builder s)
    | B.Jdconst d ->
	if d = 0.0 || d = 1.0 then 1 else 3
    | B.Jfconst f ->
	if f = JFloat.zero || f = JFloat.one || f = JFloat.two
	then 1
	else ldc_length (CP.find_float builder f)
    | B.Jiconst i ->
	if -1l <= i && i <= 5l then
	  1 (* iconst_x *)
	else if -128l <= i && i <= 127l then
	  2 (* bipush *)
	else if -0x8000l <= i && i <= 0x7fffl then
	  3 (* sipush *)
	else ldc_length (CP.find_int builder i)
    | B.Jlconst l ->
	if l = 0L || l = 1L then 1 else 3
    | B.Jcheckcast _ | B.Jgetfield _ | B.Jgetstatic _ | B.Jif_acmpeq _
    | B.Jif_acmpne _ | B.Jif_icmpeq _ | B.Jif_icmpne _ | B.Jif_icmplt _
    | B.Jif_icmpge _ | B.Jif_icmpgt _ | B.Jif_icmple _ | B.Jifeq _
    | B.Jifne _ | B.Jiflt _ | B.Jifge _ | B.Jifgt _ | B.Jifle _
    | B.Jifnonnull _ | B.Jifnull _ | B.Jinstanceof _
    | B.Jinvokespecial _ | B.Jinvokestatic _
    | B.Jinvokevirtual _ | B.Jnew _ | B.Jputfield _ | B.Jputstatic _->
	3
    | B.Jinvokeinterface _ ->
	5
    | B.Jnewarray (typ, dimension) ->
	if dimension = 1 then
	  (match typ with
	     | Jvmtype.TRef _ -> 3  (* Anewarray *)
	     | _              -> 2) (* Newarray *)
	else
	  4 (* multianewarray *)
    | B.Jiinc (var, const) ->
	if var <= 255 && -128 <= const && const <= 127 then
	  3
	else
	  6
    | B.Jgoto label
    | B.Jjsr label ->
	if Hashtbl.mem mapping label then
	  let target = Hashtbl.find mapping label in
	  let jump_offset = target - offset in
	    if -0x8000 <= jump_offset && jump_offset <= 0x7ffff then
	      3
	    else
	      5
	else
	  5 (* assume wide for now *)
    | B.Jaload lvar_idx
    | B.Jastore lvar_idx
    | B.Jdload lvar_idx
    | B.Jdstore lvar_idx 
    | B.Jfload lvar_idx
    | B.Jfstore lvar_idx
    | B.Jistore lvar_idx
    | B.Jiload lvar_idx
    | B.Jlload lvar_idx
    | B.Jlstore lvar_idx ->
	if lvar_idx <= 3 then 1
	else if lvar_idx <= 255 then 2
	else 4
    | B.Jret lvar_idx ->
	if lvar_idx <= 255 then 2
	else 4
    | B.Jlookupswitch (default, cases) ->
	1 + padding offset + 8 + 8 * List.length cases
    | B.Jtableswitch (default, low, targets) ->
	1 + padding offset + 12 + List.length targets * 4
  in
  let rec process_instrs offset instrs = match instrs with
    | [] ->
	offset
    | i::instrs ->
	let delta = instruction_length i offset in
	  process_instrs (offset + delta) instrs
  in
  let rec find_fixpoint () =
    changed := false;
    let len = process_instrs 0 instrs in
      if !changed then find_fixpoint () else len
  in
  let len = find_fixpoint () in
    mapping, len

let translate_ldc index_opt = match index_opt with
  | None -> raise (CompileBytecodeError "translate_instruction: [INTERNAL] expecting constants to already be in constant pool")
  | Some index ->
      if is_ui8 (CP.index_to_int index) then LB.Ldc index else LB.Ldc_w index

let lookup_label mapping label =
  try Hashtbl.find mapping label
  with Not_found -> raise (CompileBytecodeError "translate_instruction: label not found")

let translate_instruction builder mapping return_typ offset instr = match instr with
  | B.Jlabel (label, _) ->
      if Hashtbl.find mapping label <> offset then
	raise (CompileBytecodeError (Printf.sprintf "translate_instruction: label-offset mismatch: %d %d" (Hashtbl.find mapping label) offset))
      else
	None
  | B.Jsconst str  -> Some (translate_ldc (CP.find_string builder str))
  | B.Jaaload      -> Some LB.Aaload
  | B.Jaastore     -> Some LB.Aastore
  | B.Jaconst_null -> Some LB.Aconst_null
  | B.Jaload 0     -> Some LB.Aload_0
  | B.Jaload 1     -> Some LB.Aload_1
  | B.Jaload 2     -> Some LB.Aload_2
  | B.Jaload 3     -> Some LB.Aload_3
  | B.Jaload n when is_ui8 n -> Some (LB.Aload n)
  | B.Jaload n     -> Some (LB.Aload_w n)
  | B.Jarraylength -> Some (LB.Arraylength)
  | B.Jastore 0    -> Some LB.Astore_0
  | B.Jastore 1    -> Some LB.Astore_1
  | B.Jastore 2    -> Some LB.Astore_2
  | B.Jastore 3    -> Some LB.Astore_3
  | B.Jastore n when is_ui8 n -> Some (LB.Astore n)
  | B.Jastore n    -> Some (LB.Astore n)
  | B.Jathrow      -> Some (LB.Athrow)

  | B.Jbaload      -> Some LB.Baload
  | B.Jbastore     -> Some LB.Bastore

  | B.Jcaload      -> Some LB.Caload
  | B.Jcastore     -> Some LB.Castore
  | B.Jcheckcast r -> Some (LB.Checkcast (CP.add_class builder r))
  | B.Jclassconst r -> Some (translate_ldc (CP.find_class builder r))

  | B.Jd2f         -> Some LB.D2f
  | B.Jd2i         -> Some LB.D2i
  | B.Jd2l         -> Some LB.D2l
  | B.Jdadd        -> Some LB.Dadd
  | B.Jdaload      -> Some LB.Daload
  | B.Jdastore     -> Some LB.Dastore
  | B.Jdcmpg       -> Some LB.Dcmpg
  | B.Jdcmpl       -> Some LB.Dcmpl
  | B.Jdconst 0.0  -> Some LB.Dconst_0
  | B.Jdconst 1.0  -> Some LB.Dconst_1
  | B.Jdconst d    -> Some (LB.Ldc2_w (CP.add_double builder d))
  | B.Jddiv        -> Some LB.Ddiv
  | B.Jdload 0     -> Some LB.Dload_0
  | B.Jdload 1     -> Some LB.Dload_1
  | B.Jdload 2     -> Some LB.Dload_2
  | B.Jdload 3     -> Some LB.Dload_3
  | B.Jdload n when is_ui8 n -> Some (LB.Dload n)
  | B.Jdload n     -> Some (LB.Dload_w n)
  | B.Jdmul        -> Some LB.Dmul
  | B.Jdneg        -> Some LB.Dneg
  | B.Jdrem        -> Some LB.Drem
  | B.Jdstore 0    -> Some LB.Dstore_0
  | B.Jdstore 1    -> Some LB.Dstore_1
  | B.Jdstore 2    -> Some LB.Dstore_2
  | B.Jdstore 3    -> Some LB.Dstore_3
  | B.Jdstore n when is_ui8 n -> Some (LB.Dstore n)
  | B.Jdstore n    -> Some (LB.Dstore_w n)
  | B.Jdsub        -> Some LB.Dsub
  | B.Jdup         -> Some LB.Dup
  | B.Jdup_x1      -> Some LB.Dup_x1
  | B.Jdup_x2      -> Some LB.Dup_x2
  | B.Jdup2        -> Some LB.Dup2
  | B.Jdup2_x1     -> Some LB.Dup2_x1
  | B.Jdup2_x2     -> Some LB.Dup2_x2

  | B.Jf2d         -> Some LB.F2d
  | B.Jf2i         -> Some LB.F2i
  | B.Jf2l         -> Some LB.F2l
  | B.Jfadd        -> Some LB.Fadd
  | B.Jfaload      -> Some LB.Faload
  | B.Jfastore     -> Some LB.Fastore
  | B.Jfcmpg       -> Some LB.Fcmpg
  | B.Jfcmpl       -> Some LB.Fcmpl
  | B.Jfconst f    ->
      if f = JFloat.zero then Some (LB.Fconst_0)
      else if f = JFloat.one then Some (LB.Fconst_1)
      else if f = JFloat.two then Some (LB.Fconst_2)
      else Some (translate_ldc (CP.find_float builder f))
  | B.Jfdiv        -> Some LB.Fdiv
  | B.Jfload 0     -> Some LB.Fload_0
  | B.Jfload 1     -> Some LB.Fload_1
  | B.Jfload 2     -> Some LB.Fload_2
  | B.Jfload 3     -> Some LB.Fload_3
  | B.Jfload n when is_ui8 n -> Some (LB.Fload n)
  | B.Jfload n     -> Some (LB.Fload_w n)
  | B.Jfmul        -> Some LB.Fmul
  | B.Jfneg        -> Some LB.Fneg
  | B.Jfrem        -> Some LB.Frem
  | B.Jfstore 0    -> Some LB.Fstore_0
  | B.Jfstore 1    -> Some LB.Fstore_1
  | B.Jfstore 2    -> Some LB.Fstore_2
  | B.Jfstore 3    -> Some LB.Fstore_3
  | B.Jfstore n when is_ui8 n -> Some (LB.Fstore n)
  | B.Jfstore n    -> Some (LB.Fstore_w n)
  | B.Jfsub        -> Some LB.Fsub

  | B.Jgetfield (cls,fname,ftype)  -> Some (LB.Getfield (CP.add_field_ref builder (cls,fname,ftype)))
  | B.Jgetstatic (cls,fname,ftype) -> Some (LB.Getstatic (CP.add_field_ref builder (cls,fname,ftype)))
  | B.Jgoto label ->
      let target = lookup_label mapping label in
      let jump_offset = target - offset in
	Some (if -0x8000 <= jump_offset && jump_offset <= 0x7ffff then
		LB.Goto jump_offset
	      else
		LB.Goto_w (Int32.of_int jump_offset))

  | B.Ji2b         -> Some LB.I2b
  | B.Ji2c         -> Some LB.I2c
  | B.Ji2d         -> Some LB.I2d
  | B.Ji2f         -> Some LB.I2f
  | B.Ji2l         -> Some LB.I2l
  | B.Ji2s         -> Some LB.I2s
  | B.Jiadd        -> Some LB.Iadd
  | B.Jiaload      -> Some LB.Iaload
  | B.Jiand        -> Some LB.Iand
  | B.Jiastore     -> Some LB.Iastore
  | B.Jiconst -1l  -> Some LB.Iconst_m1
  | B.Jiconst 0l   -> Some LB.Iconst_0
  | B.Jiconst 1l   -> Some LB.Iconst_1
  | B.Jiconst 2l   -> Some LB.Iconst_2
  | B.Jiconst 3l   -> Some LB.Iconst_3
  | B.Jiconst 4l   -> Some LB.Iconst_4
  | B.Jiconst 5l   -> Some LB.Iconst_5
  | B.Jiconst n when is_i8 n  -> Some (LB.Bipush (Int32.to_int n))
  | B.Jiconst n when is_i16 n -> Some (LB.Sipush (Int32.to_int n))
  | B.Jiconst n    -> Some (translate_ldc (CP.find_int builder n))
  | B.Jidiv        -> Some LB.Idiv
  | B.Jif_acmpeq l -> Some (LB.If_acmpeq (lookup_label mapping l - offset))
  | B.Jif_acmpne l -> Some (LB.If_acmpne (lookup_label mapping l - offset))
  | B.Jif_icmpeq l -> Some (LB.If_icmpeq (lookup_label mapping l - offset))
  | B.Jif_icmpne l -> Some (LB.If_icmpne (lookup_label mapping l - offset))
  | B.Jif_icmplt l -> Some (LB.If_icmplt (lookup_label mapping l - offset))
  | B.Jif_icmpge l -> Some (LB.If_icmpge (lookup_label mapping l - offset))
  | B.Jif_icmpgt l -> Some (LB.If_icmpgt (lookup_label mapping l - offset))
  | B.Jif_icmple l -> Some (LB.If_icmple (lookup_label mapping l - offset))
  | B.Jifeq l      -> Some (LB.Ifeq (lookup_label mapping l - offset))
  | B.Jifne l      -> Some (LB.Ifne (lookup_label mapping l - offset))
  | B.Jiflt l      -> Some (LB.Iflt (lookup_label mapping l - offset))
  | B.Jifge l      -> Some (LB.Ifge (lookup_label mapping l - offset))
  | B.Jifgt l      -> Some (LB.Ifgt (lookup_label mapping l - offset))
  | B.Jifle l      -> Some (LB.Ifle (lookup_label mapping l - offset))
  | B.Jifnonnull l -> Some (LB.Ifnonnull (lookup_label mapping l - offset))
  | B.Jifnull l    -> Some (LB.Ifnull (lookup_label mapping l - offset))
  | B.Jiinc (var, const) ->
      if is_ui8 var && -128 <= const && const <= 127 then
	Some (LB.Iinc (var, const))
      else if is_ui16 var && is_i16 (Int32.of_int const) then
	Some (LB.Iinc_w (var, const))
      else raise (CompileBytecodeError "translate_instruction: overflow in Jiinc instruction")
  | B.Jiload 0     -> Some LB.Iload_0
  | B.Jiload 1     -> Some LB.Iload_1
  | B.Jiload 2     -> Some LB.Iload_2
  | B.Jiload 3     -> Some LB.Iload_3
  | B.Jiload n when is_ui8 n -> Some (LB.Iload n)
  | B.Jiload n     -> Some (LB.Iload_w n)
  | B.Jimul        -> Some LB.Imul
  | B.Jineg        -> Some LB.Ineg
  | B.Jinstanceof r -> Some (LB.Instanceof (CP.add_class builder r))
  | B.Jinvokeinterface (mclass, mname, msig) -> Some (LB.Invokeinterface (CP.add_imethod_ref builder (mclass, mname, msig), 1))
  | B.Jinvokespecial (mclass, mname, msig)   -> Some (LB.Invokespecial (CP.add_method_ref builder (mclass, mname, msig)))
  | B.Jinvokestatic (mclass, mname, msig)    -> Some (LB.Invokestatic (CP.add_method_ref builder (mclass, mname, msig)))
  | B.Jinvokevirtual (mclass, mname, msig)   -> Some (LB.Invokevirtual (CP.add_method_ref builder (mclass, mname, msig)))
  | B.Jior         -> Some LB.Ior
  | B.Jirem        -> Some LB.Irem
  | B.Jishl        -> Some LB.Ishl
  | B.Jishr        -> Some LB.Ishr
  | B.Jistore 0    -> Some LB.Istore_0
  | B.Jistore 1    -> Some LB.Istore_1
  | B.Jistore 2    -> Some LB.Istore_2
  | B.Jistore 3    -> Some LB.Istore_3
  | B.Jistore n when is_ui8 n -> Some (LB.Istore n)
  | B.Jistore n    -> Some (LB.Istore_w n)
  | B.Jisub        -> Some LB.Isub
  | B.Jiushr       -> Some LB.Iushr
  | B.Jixor        -> Some LB.Ixor

  | B.Jjsr label   ->
      let target = lookup_label mapping label in
      let jump_offset = target - offset in
	Some (if -0x8000 <= jump_offset && jump_offset <= 0x7ffff then
		LB.Jsr jump_offset
	      else
		LB.Jsr_w (Int32.of_int jump_offset))

  | B.Jl2d         -> Some LB.L2d
  | B.Jl2f         -> Some LB.L2f
  | B.Jl2i         -> Some LB.L2i
  | B.Jladd        -> Some LB.Ladd
  | B.Jlaload      -> Some LB.Laload
  | B.Jland        -> Some LB.Land
  | B.Jlastore     -> Some LB.Lastore
  | B.Jlcmp        -> Some LB.Lcmp
  | B.Jlconst 0L   -> Some LB.Lconst_0
  | B.Jlconst 1L   -> Some LB.Lconst_1
  | B.Jlconst n    -> Some (LB.Ldc2_w (CP.add_long builder n))
  | B.Jldiv        -> Some LB.Ldiv
  | B.Jlload 0     -> Some LB.Lload_0
  | B.Jlload 1     -> Some LB.Lload_1
  | B.Jlload 2     -> Some LB.Lload_2
  | B.Jlload 3     -> Some LB.Lload_3
  | B.Jlload n when is_ui8 n -> Some (LB.Lload n)
  | B.Jlload n     -> Some (LB.Lload_w n)
  | B.Jlmul        -> Some LB.Lmul
  | B.Jlneg        -> Some LB.Lneg
  | B.Jlookupswitch (default, cases) ->
      let default_jump = Int32.of_int (lookup_label mapping default - offset) in
      let match_offsets = List.map (fun (i,l) -> (i, Int32.of_int (lookup_label mapping l - offset))) cases in
	Some (LB.Lookupswitch (default_jump, match_offsets))
  | B.Jlor         -> Some LB.Lor
  | B.Jlrem        -> Some LB.Lrem
  | B.Jlshl        -> Some LB.Lshl
  | B.Jlshr        -> Some LB.Lshr
  | B.Jlstore 0    -> Some LB.Lstore_0
  | B.Jlstore 1    -> Some LB.Lstore_1
  | B.Jlstore 2    -> Some LB.Lstore_2
  | B.Jlstore 3    -> Some LB.Lstore_3
  | B.Jlstore n when is_ui8 n -> Some (LB.Lstore n)
  | B.Jlstore n    -> Some (LB.Lstore_w n)
  | B.Jlsub        -> Some LB.Lsub
  | B.Jlushr       -> Some LB.Lushr
  | B.Jlxor        -> Some LB.Lxor

  | B.Jmonitorenter -> Some LB.Monitorenter
  | B.Jmonitorexit  -> Some LB.Monitorexit

  | B.Jnew r        -> Some (LB.New (CP.add_class builder (Jvmtype.TObject r)))
  | B.Jnewarray (typ, dimension) ->
      if dimension < 1 then
	raise (CompileBytecodeError "Jnewarray with dimension < 1")
      else if dimension = 1 then
	Some (match typ with
		| Jvmtype.TBoolean -> LB.Newarray LB.Array_boolean
		| Jvmtype.TChar    -> LB.Newarray LB.Array_char
		| Jvmtype.TFloat   -> LB.Newarray LB.Array_float
		| Jvmtype.TDouble  -> LB.Newarray LB.Array_double
		| Jvmtype.TByte    -> LB.Newarray LB.Array_byte
		| Jvmtype.TShort   -> LB.Newarray LB.Array_short
		| Jvmtype.TInt     -> LB.Newarray LB.Array_int
		| Jvmtype.TLong    -> LB.Newarray LB.Array_long
		| Jvmtype.TRef t   -> LB.Anewarray (CP.add_class builder t))
      else
	let rec add_arrays n t = if n = 1 then Jvmtype.TArray t else Jvmtype.TArray (Jvmtype.TRef (add_arrays (n-1) t))
	in
	  Some (LB.Multianewarray (CP.add_class builder (add_arrays dimension typ), dimension))
  | B.Jnop          -> Some LB.Nop
  
  | B.Jpop          -> Some LB.Pop
  | B.Jpop2         -> Some LB.Pop2
  | B.Jputfield (cls,fname,ftype)  -> Some (LB.Putfield (CP.add_field_ref builder (cls,fname,ftype)))
  | B.Jputstatic (cls,fname,ftype) -> Some (LB.Putstatic (CP.add_field_ref builder (cls,fname,ftype)))

  | B.Jret n when is_ui8 n -> Some (LB.Ret n)
  | B.Jret n        -> Some (LB.Ret_w n)
  | B.Jreturn       ->
      Some (match return_typ with
	      | Some (Jvmtype.TBoolean) -> LB.Ireturn
	      | Some (Jvmtype.TChar)    -> LB.Ireturn
	      | Some (Jvmtype.TFloat)   -> LB.Freturn
	      | Some (Jvmtype.TDouble)  -> LB.Dreturn
	      | Some (Jvmtype.TByte)    -> LB.Ireturn
	      | Some (Jvmtype.TShort)   -> LB.Ireturn
	      | Some (Jvmtype.TInt)     -> LB.Ireturn
	      | Some (Jvmtype.TLong)    -> LB.Lreturn
	      | Some (Jvmtype.TRef _)   -> LB.Areturn
	      | None                    -> LB.Return)

  | B.Jsaload  -> Some LB.Saload
  | B.Jsastore -> Some LB.Sastore
  | B.Jswap    -> Some LB.Swap

  | B.Jtableswitch (default, low, labels) ->
      let offsets = List.map (fun l -> Int32.of_int (lookup_label mapping l)) labels in
      let default_jump = Int32.of_int (lookup_label mapping default) in
	Some (LB.Tableswitch (default_jump, low, offsets))

let compile_bytecode ~builder ~return_typ ~instrs =
  let _            = add_constants_to_pool builder instrs in
  let mapping, len = create_label_table builder instrs in
  let _            = if len > 0xffff then raise (CompileBytecodeError "Length of bytecode too long") in
  let code         = Array.make len None in
  let rec translate_loop offset instrs = match instrs with
    | [] -> ()
    | i::instrs ->
	(match translate_instruction builder mapping return_typ offset i with
	   | None -> translate_loop offset instrs
	   | Some op ->
	       code.(offset) <- Some op;
	       translate_loop (offset + LB.instruction_length op offset) instrs)
  in
    translate_loop 0 instrs;
    code, mapping


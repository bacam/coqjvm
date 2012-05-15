open CoqModules
open TranslateAnnos

module JT = Ocaml_jvml.Jvmtype
module LB = Ocaml_jvml.LowlevelBytecode
module CP = Ocaml_jvml.Constpool
module CF = Ocaml_jvml.Classfile
module AF = Ocaml_jvml.AccessFlags

let rec trans_type ty = match ty with
  | JT.TByte    -> C.Coq_ty_byte
  | JT.TChar    -> C.Coq_ty_char
  | JT.TDouble  -> C.Coq_ty_double
  | JT.TFloat   -> C.Coq_ty_float
  | JT.TInt     -> C.Coq_ty_int
  | JT.TLong    -> C.Coq_ty_long
  | JT.TShort   -> C.Coq_ty_short
  | JT.TBoolean -> C.Coq_ty_boolean
  | JT.TRef ty  -> C.Coq_ty_ref (trans_ref_type ty)
and trans_ref_type ty = match ty with
  | JT.TObject classname -> C.Coq_ty_obj classname
  | JT.TArray ty         -> C.Coq_ty_arr (trans_type ty)

let trans_array_type ty = match ty with
  | LB.Array_boolean -> C.Coq_aty_boolean
  | LB.Array_char    -> C.Coq_aty_char
  | LB.Array_float   -> C.Coq_aty_float
  | LB.Array_double  -> C.Coq_aty_double
  | LB.Array_byte    -> C.Coq_aty_byte
  | LB.Array_short   -> C.Coq_aty_short
  | LB.Array_int     -> C.Coq_aty_int
  | LB.Array_long    -> C.Coq_aty_long

let trans_method_descriptor (args, retty) =
  { C.descriptor_ret_type  = Option.map trans_type retty
  ; C.descriptor_arg_types = List.map trans_type args
  }

let trans_opcode pos_table jvm_pos coq_pos op =
  let trans_offset offset =
    let coq_target = pos_table.(jvm_pos + offset) in
    let coq_offset = coq_target - coq_pos in
      Coqutil.z_of_int coq_offset
  in match op with
    | LB.Aaload      -> C.Coq_op_aaload
    | LB.Aastore     -> C.Coq_op_aastore
    | LB.Aconst_null -> C.Coq_op_aconst_null
    | LB.Aload i      
    | LB.Aload_w i   -> C.Coq_op_load (C.Coq_sty_addr, Common.Types.nat_of_int i)
    | LB.Aload_0     -> C.Coq_op_load (C.Coq_sty_addr, Common.Types.nat_of_int 0)
    | LB.Aload_1     -> C.Coq_op_load (C.Coq_sty_addr, Common.Types.nat_of_int 1)
    | LB.Aload_2     -> C.Coq_op_load (C.Coq_sty_addr, Common.Types.nat_of_int 2)
    | LB.Aload_3     -> C.Coq_op_load (C.Coq_sty_addr, Common.Types.nat_of_int 3)
    | LB.Anewarray i -> C.Coq_op_anewarray i
    | LB.Areturn     -> C.Coq_op_valreturn C.Coq_sty_addr
    | LB.Arraylength -> C.Coq_op_arraylength
    | LB.Astore i
    | LB.Astore_w i  -> C.Coq_op_store (C.Coq_sty_addr, Common.Types.nat_of_int i)
    | LB.Astore_0    -> C.Coq_op_store (C.Coq_sty_addr, Common.Types.nat_of_int 0)
    | LB.Astore_1    -> C.Coq_op_store (C.Coq_sty_addr, Common.Types.nat_of_int 1)
    | LB.Astore_2    -> C.Coq_op_store (C.Coq_sty_addr, Common.Types.nat_of_int 2)
    | LB.Astore_3    -> C.Coq_op_store (C.Coq_sty_addr, Common.Types.nat_of_int 3)
    | LB.Athrow      -> C.Coq_op_athrow
	(* B *)
    | LB.Baload      -> C.Coq_op_baload
    | LB.Bastore     -> C.Coq_op_bastore
    | LB.Bipush i    -> C.Coq_op_iconst (Int32.of_int i)
	(* C *)
    | LB.Caload      -> C.Coq_op_caload
    | LB.Castore     -> C.Coq_op_castore
    | LB.Checkcast i -> C.Coq_op_checkcast i
	(* D *)
    | LB.D2f         -> failwith "Unimplemented: d2f"
    | LB.D2i         -> failwith "Unimplemented: d2i"
    | LB.D2l         -> failwith "Unimplemented: d2l"
    | LB.Dadd        -> failwith "Unimplemented: dadd"
    | LB.Daload      -> C.Coq_op_daload
    | LB.Dastore     -> C.Coq_op_dastore
    | LB.Dcmpg       -> failwith "Unimplemented: dcmpg"
    | LB.Dcmpl       -> failwith "Unimplemented: dcmpl"
    | LB.Dconst_0    -> failwith "Unimplemented: dconst_0"
    | LB.Dconst_1    -> failwith "Unimplemented: dconst_1"
    | LB.Ddiv        -> failwith "Unimplemented: ddiv"
    | LB.Dload i
    | LB.Dload_w i   -> C.Coq_op_load (C.Coq_sty_double, Common.Types.nat_of_int i)
    | LB.Dload_0     -> C.Coq_op_load (C.Coq_sty_double, Common.Types.nat_of_int 0)
    | LB.Dload_1     -> C.Coq_op_load (C.Coq_sty_double, Common.Types.nat_of_int 1)
    | LB.Dload_2     -> C.Coq_op_load (C.Coq_sty_double, Common.Types.nat_of_int 2)
    | LB.Dload_3     -> C.Coq_op_load (C.Coq_sty_double, Common.Types.nat_of_int 3)
    | LB.Dmul        -> failwith "Unimplemented: dmul"
    | LB.Dneg        -> failwith "Unimplemented: dneg"
    | LB.Drem        -> failwith "Unimplemented: drem"
    | LB.Dreturn     -> C.Coq_op_valreturn C.Coq_sty_double
    | LB.Dstore i
    | LB.Dstore_w i  -> C.Coq_op_store (C.Coq_sty_double, Common.Types.nat_of_int i)
    | LB.Dstore_0    -> C.Coq_op_store (C.Coq_sty_double, Common.Types.nat_of_int 0)
    | LB.Dstore_1    -> C.Coq_op_store (C.Coq_sty_double, Common.Types.nat_of_int 1)
    | LB.Dstore_2    -> C.Coq_op_store (C.Coq_sty_double, Common.Types.nat_of_int 2)
    | LB.Dstore_3    -> C.Coq_op_store (C.Coq_sty_double, Common.Types.nat_of_int 3)
    | LB.Dsub        -> failwith "Unimplemented: dsub"
    | LB.Dup         -> C.Coq_op_dup
    | LB.Dup_x1      -> C.Coq_op_dup_x1
    | LB.Dup_x2      -> C.Coq_op_dup_x2
    | LB.Dup2        -> C.Coq_op_dup2
    | LB.Dup2_x1     -> C.Coq_op_dup2_x1
    | LB.Dup2_x2     -> C.Coq_op_dup2_x2
	(* F *)
    | LB.F2d         -> failwith "Unimplemented: f2d"
    | LB.F2i         -> failwith "Unimplemented: f2i"
    | LB.F2l         -> failwith "Unimplemented: f2l"
    | LB.Fadd        -> failwith "Unimplemented: fadd"
    | LB.Faload      -> C.Coq_op_faload
    | LB.Fastore     -> C.Coq_op_fastore
    | LB.Fcmpg       -> failwith "Unimplemented: fcmpg"
    | LB.Fcmpl       -> failwith "Unimplemented: fcmpl"
    | LB.Fconst_0    -> failwith "Unimplemented: fconst_0"
    | LB.Fconst_1    -> failwith "Unimplemented: fconst_1"
    | LB.Fconst_2    -> failwith "Unimplemented: fconst_2"
    | LB.Fdiv        -> failwith "Unimplemented: fdiv"
    | LB.Fload i
    | LB.Fload_w i   -> C.Coq_op_load (C.Coq_sty_float, Common.Types.nat_of_int i)
    | LB.Fload_0     -> C.Coq_op_load (C.Coq_sty_float, Common.Types.nat_of_int 0)
    | LB.Fload_1     -> C.Coq_op_load (C.Coq_sty_float, Common.Types.nat_of_int 1)
    | LB.Fload_2     -> C.Coq_op_load (C.Coq_sty_float, Common.Types.nat_of_int 2)
    | LB.Fload_3     -> C.Coq_op_load (C.Coq_sty_float, Common.Types.nat_of_int 3)
    | LB.Fmul        -> failwith "Unimplemented: fmul"
    | LB.Fneg        -> failwith "Unimplemented: fneg"
    | LB.Frem        -> failwith "Unimplemented: frem"
    | LB.Freturn     -> C.Coq_op_valreturn C.Coq_sty_float
    | LB.Fstore i
    | LB.Fstore_w i  -> C.Coq_op_store (C.Coq_sty_float, Common.Types.nat_of_int i)
    | LB.Fstore_0    -> C.Coq_op_store (C.Coq_sty_float, Common.Types.nat_of_int 0)
    | LB.Fstore_1    -> C.Coq_op_store (C.Coq_sty_float, Common.Types.nat_of_int 1)
    | LB.Fstore_2    -> C.Coq_op_store (C.Coq_sty_float, Common.Types.nat_of_int 2)
    | LB.Fstore_3    -> C.Coq_op_store (C.Coq_sty_float, Common.Types.nat_of_int 3)
    | LB.Fsub        -> failwith "Unimplemented: fsub"
	(* G *)
    | LB.Getfield i  -> C.Coq_op_getfield i
    | LB.Getstatic i -> C.Coq_op_getstatic i
    | LB.Goto offset -> C.Coq_op_goto (trans_offset offset)
    | LB.Goto_w offset -> C.Coq_op_goto (trans_offset (Int32.to_int offset))
	(* I *)
    | LB.I2b         -> failwith "Unimplemented: i2b"
    | LB.I2c         -> failwith "Unimplemented: i2c"
    | LB.I2d         -> failwith "Unimplemented: i2d"
    | LB.I2f         -> failwith "Unimplemented: i2f"
    | LB.I2l         -> failwith "Unimplemented: i2l"
    | LB.I2s         -> failwith "Unimplemented: i2s"
    | LB.Iadd        -> C.Coq_op_iarithb C.Coq_iadd
    | LB.Iaload      -> C.Coq_op_iaload
    | LB.Iand        -> C.Coq_op_iarithb C.Coq_iand
    | LB.Iastore     -> C.Coq_op_iastore
    | LB.Iconst_m1   -> C.Coq_op_iconst (-1l)
    | LB.Iconst_0    -> C.Coq_op_iconst 0l
    | LB.Iconst_1    -> C.Coq_op_iconst 1l
    | LB.Iconst_2    -> C.Coq_op_iconst 2l
    | LB.Iconst_3    -> C.Coq_op_iconst 3l
    | LB.Iconst_4    -> C.Coq_op_iconst 4l
    | LB.Iconst_5    -> C.Coq_op_iconst 5l
    | LB.Idiv        -> C.Coq_op_iarithb C.Coq_idiv
    | LB.If_acmpeq i -> C.Coq_op_if_acmp (C.Coq_acmp_eq, trans_offset i)
    | LB.If_acmpne i -> C.Coq_op_if_acmp (C.Coq_acmp_ne, trans_offset i)
    | LB.If_icmpeq i -> C.Coq_op_if_icmp (C.Coq_cmp_eq, trans_offset i)
    | LB.If_icmpne i -> C.Coq_op_if_icmp (C.Coq_cmp_ne, trans_offset i)
    | LB.If_icmplt i -> C.Coq_op_if_icmp (C.Coq_cmp_lt, trans_offset i)
    | LB.If_icmpge i -> C.Coq_op_if_icmp (C.Coq_cmp_ge, trans_offset i)
    | LB.If_icmpgt i -> C.Coq_op_if_icmp (C.Coq_cmp_gt, trans_offset i)
    | LB.If_icmple i -> C.Coq_op_if_icmp (C.Coq_cmp_le, trans_offset i)
    | LB.Ifeq i      -> C.Coq_op_if (C.Coq_cmp_eq, trans_offset i)
    | LB.Ifne i      -> C.Coq_op_if (C.Coq_cmp_ne, trans_offset i)
    | LB.Iflt i      -> C.Coq_op_if (C.Coq_cmp_lt, trans_offset i)
    | LB.Ifge i      -> C.Coq_op_if (C.Coq_cmp_ge, trans_offset i)
    | LB.Ifgt i      -> C.Coq_op_if (C.Coq_cmp_gt, trans_offset i)
    | LB.Ifle i      -> C.Coq_op_if (C.Coq_cmp_le, trans_offset i)
    | LB.Ifnonnull i -> C.Coq_op_ifnonnull (trans_offset i)
    | LB.Ifnull i    -> C.Coq_op_ifnull (trans_offset i)
    | LB.Iinc (i1,i2)
    | LB.Iinc_w (i1,i2) -> C.Coq_op_iinc (Common.Types.nat_of_int i1, Int32.of_int i2)
    | LB.Iload i
    | LB.Iload_w i   -> C.Coq_op_load (C.Coq_sty_int, Common.Types.nat_of_int i)
    | LB.Iload_0     -> C.Coq_op_load (C.Coq_sty_int, Common.Types.nat_of_int 0)
    | LB.Iload_1     -> C.Coq_op_load (C.Coq_sty_int, Common.Types.nat_of_int 1)
    | LB.Iload_2     -> C.Coq_op_load (C.Coq_sty_int, Common.Types.nat_of_int 2)
    | LB.Iload_3     -> C.Coq_op_load (C.Coq_sty_int, Common.Types.nat_of_int 3)
    | LB.Imul        -> C.Coq_op_iarithb C.Coq_imul
    | LB.Ineg        -> C.Coq_op_iarithu C.Coq_ineg
    | LB.Instanceof i -> C.Coq_op_instanceof i
    | LB.Invokeinterface (i,_) -> C.Coq_op_invokeinterface i
    | LB.Invokespecial i   -> C.Coq_op_invokespecial i
    | LB.Invokestatic i    -> C.Coq_op_invokestatic i
    | LB.Invokevirtual i   -> C.Coq_op_invokevirtual i
    | LB.Ior         -> C.Coq_op_iarithb C.Coq_ior
    | LB.Irem        -> C.Coq_op_iarithb C.Coq_irem
    | LB.Ireturn     -> C.Coq_op_valreturn C.Coq_sty_int
    | LB.Ishl        -> C.Coq_op_iarithb C.Coq_ishl
    | LB.Ishr        -> C.Coq_op_iarithb C.Coq_ishr
    | LB.Istore i
    | LB.Istore_w i  -> C.Coq_op_store (C.Coq_sty_int, Common.Types.nat_of_int i)
    | LB.Istore_0    -> C.Coq_op_store (C.Coq_sty_int, Common.Types.nat_of_int 0)
    | LB.Istore_1    -> C.Coq_op_store (C.Coq_sty_int, Common.Types.nat_of_int 1)
    | LB.Istore_2    -> C.Coq_op_store (C.Coq_sty_int, Common.Types.nat_of_int 2)
    | LB.Istore_3    -> C.Coq_op_store (C.Coq_sty_int, Common.Types.nat_of_int 3)
    | LB.Isub        -> C.Coq_op_iarithb C.Coq_isub
    | LB.Iushr       -> C.Coq_op_iarithb C.Coq_iushr
    | LB.Ixor        -> C.Coq_op_iarithb C.Coq_ixor
	(* J *)
    | LB.Jsr _
    | LB.Jsr_w _     -> failwith "Unimplemented: jsr(_w)"
	(* L *)
    | LB.L2d         -> failwith "Unimplemented: l2d"
    | LB.L2f         -> failwith "Unimplemented: l2f"
    | LB.L2i         -> failwith "Unimplemented: l2i"
    | LB.Ladd        -> C.Coq_op_larithb C.Coq_iadd
    | LB.Laload      -> C.Coq_op_laload
    | LB.Land        -> C.Coq_op_larithb C.Coq_iand
    | LB.Lastore     -> C.Coq_op_lastore
    | LB.Lcmp        -> C.Coq_op_lcmp
    | LB.Lconst_0    -> C.Coq_op_lconst C.Coq_l0
    | LB.Lconst_1    -> C.Coq_op_lconst C.Coq_l1
    | LB.Ldc i       -> C.Coq_op_ldc i
    | LB.Ldc_w i
    | LB.Ldc2_w i    -> C.Coq_op_ldc2 i (* FIXME: is this correct for Ldc_w? *)
    | LB.Ldiv        -> C.Coq_op_larithb C.Coq_idiv
    | LB.Lload i
    | LB.Lload_w i   -> C.Coq_op_load (C.Coq_sty_long, Common.Types.nat_of_int i)
    | LB.Lload_0     -> C.Coq_op_load (C.Coq_sty_long, Common.Types.nat_of_int 0)
    | LB.Lload_1     -> C.Coq_op_load (C.Coq_sty_long, Common.Types.nat_of_int 1)
    | LB.Lload_2     -> C.Coq_op_load (C.Coq_sty_long, Common.Types.nat_of_int 2)
    | LB.Lload_3     -> C.Coq_op_load (C.Coq_sty_long, Common.Types.nat_of_int 3)
    | LB.Lmul        -> C.Coq_op_larithb C.Coq_imul
    | LB.Lneg        -> C.Coq_op_larithu C.Coq_ineg
    | LB.Lookupswitch _ -> failwith "Unimplemented: lookupswitch"
    | LB.Lor         -> C.Coq_op_larithb C.Coq_ior
    | LB.Lrem        -> C.Coq_op_larithb C.Coq_irem
    | LB.Lreturn     -> C.Coq_op_valreturn C.Coq_sty_long
    | LB.Lshl        -> C.Coq_op_larithb C.Coq_ishl
    | LB.Lshr        -> C.Coq_op_larithb C.Coq_ishr
    | LB.Lstore i
    | LB.Lstore_w i  -> C.Coq_op_store (C.Coq_sty_long, Common.Types.nat_of_int i)
    | LB.Lstore_0    -> C.Coq_op_store (C.Coq_sty_long, Common.Types.nat_of_int 0)
    | LB.Lstore_1    -> C.Coq_op_store (C.Coq_sty_long, Common.Types.nat_of_int 1)
    | LB.Lstore_2    -> C.Coq_op_store (C.Coq_sty_long, Common.Types.nat_of_int 2)
    | LB.Lstore_3    -> C.Coq_op_store (C.Coq_sty_long, Common.Types.nat_of_int 3)
    | LB.Lsub        -> C.Coq_op_larithb C.Coq_isub
    | LB.Lushr       -> C.Coq_op_larithb C.Coq_iushr
    | LB.Lxor        -> C.Coq_op_larithb C.Coq_ixor
	(* M *)
    | LB.Monitorenter -> C.Coq_op_monitorenter
    | LB.Monitorexit  -> C.Coq_op_monitorexit
    | LB.Multianewarray (i,d) -> C.Coq_op_multianewarray (i,Common.Types.nat_of_int d)
	(* N *)
    | LB.New i        -> C.Coq_op_new i
    | LB.Newarray ty  -> C.Coq_op_newarray (trans_array_type ty)
    | LB.Nop          -> C.Coq_op_nop
	(* P *)
    | LB.Pop          -> C.Coq_op_pop
    | LB.Pop2         -> C.Coq_op_pop2
    | LB.Putfield i   -> C.Coq_op_putfield i
    | LB.Putstatic i  -> C.Coq_op_putstatic i
	(* R *)
    | LB.Ret _
    | LB.Ret_w _      -> failwith "Unimplemented: ret(_w)"
    | LB.Return       -> C.Coq_op_return
	(* S *)
    | LB.Saload       -> C.Coq_op_saload
    | LB.Sastore      -> C.Coq_op_sastore
    | LB.Sipush i     -> C.Coq_op_iconst (Int32.of_int i)
    | LB.Swap         -> C.Coq_op_swap
	(* T *)
    | LB.Tableswitch _ -> failwith "Unimplemented: tableswitch"

let trans_constant_pool pool =
  let trans_pool_entry e = match e with
    | CP.CPmethodref (clsnm_idx, desc_idx) ->
	let clsnm = CP.lookup_class_notarray pool clsnm_idx in
	let mnm, msig = CP.lookup_methoddesc pool desc_idx in
	  C.Coq_cpe_methodref (clsnm, mnm, trans_method_descriptor msig)
    | CP.CPimethodref (clsnm_idx, desc_idx) ->
	let clsnm = CP.lookup_class_notarray pool clsnm_idx in
	let mnm, msig = CP.lookup_methoddesc pool desc_idx in
	  C.Coq_cpe_interfacemethodref (clsnm, mnm, trans_method_descriptor msig)
    | CP.CPfieldref (clsnm_idx, desc_idx) ->
	let clsnm = CP.lookup_class_notarray pool clsnm_idx in
	let fnm, ftype = CP.lookup_fielddesc pool desc_idx in
	  C.Coq_cpe_fieldref (clsnm, fnm, trans_type ftype)
    (* FIXME: this breaks for classrefs of arrays *)
    | CP.CPclass idx ->
	(match JT.reftype_of_string (CP.lookup_utf8 pool idx) with
	   | Some (JT.TObject clsnm) -> C.Coq_cpe_classref clsnm
	   | _ -> failwith "Invalid reference type name in constant pool")
    | _ ->
	C.Coq_cpe_other
  in
  let coq_pool = ref C.ConstantPool.empty in (* FIXME: do CP.fold *)
    CP.iteri (fun i e -> coq_pool := C.ConstantPool.update !coq_pool i (trans_pool_entry e)) pool;
    !coq_pool

let rec find_code attrs = match attrs with
  | []                                                                               -> None
  | CF.Attribute (_, CF.Attr_Code (max_stack, max_locals, code, handlers, attrs))::_ -> Some (max_stack, max_locals, code, handlers, attrs)
  | _::attrs                                                                         -> find_code attrs

let trans_code pool (max_stack, max_locals, code, handlers, attrs) =
  let pos_table =
    let table = Array.make (Array.length code) (-1) in
    let coq_code_pos = ref 0 in
      Array.iteri (fun i op -> match op with None -> () | _ -> (table.(i) <- !coq_code_pos; incr coq_code_pos)) code;
      table
  in
  let rev_coq_code = ref [] in
  let coq_code_pos = ref 0 in
  let () = Array.iteri (fun i op ->
    match op with
      | None    -> ()
      | Some op -> rev_coq_code := (trans_opcode pos_table i (!coq_code_pos) op)::(!rev_coq_code); incr coq_code_pos) code in
  let trans_exn_handler h =
    { C.exc_start_pc   = Common.Types.nat_of_int pos_table.(h.CF.exn_start)
    ; C.exc_end_pc     = Common.Types.nat_of_int pos_table.(h.CF.exn_end)
    ; C.exc_handler_pc = Common.Types.nat_of_int pos_table.(h.CF.exn_pc)
    ; C.exc_catch_type = h.CF.exn_type
    }
  in
    { C.precode_max_lvars       = Common.Types.nat_of_int max_locals
    ; C.precode_max_stack       = Common.Types.nat_of_int max_stack
    ; C.precode_annot           = trans_code_annot pool pos_table attrs
    ; C.precode_exception_table = List.map trans_exn_handler handlers
    ; C.precode_code            = List.rev (!rev_coq_code)
    }

let trans_method pool m =
  { C.premethod_name         = CP.lookup_utf8 pool m.CF.m_name
  ; C.premethod_descriptor   = trans_method_descriptor (CP.lookup_methodsig pool m.CF.m_desc)
  ; C.premethod_public       = m.CF.m_flags.AF.m_public
  ; C.premethod_protected    = m.CF.m_flags.AF.m_protected
  ; C.premethod_private      = m.CF.m_flags.AF.m_private
  ; C.premethod_abstract     = m.CF.m_flags.AF.m_abstract
  ; C.premethod_static       = m.CF.m_flags.AF.m_static
  ; C.premethod_final        = m.CF.m_flags.AF.m_final
  ; C.premethod_synchronized = m.CF.m_flags.AF.m_synchronized
  ; C.premethod_strict       = m.CF.m_flags.AF.m_strictfp
  ; C.premethod_annot        = trans_method_annot pool m
  ; C.premethod_code         = Option.map (trans_code pool) (find_code m.CF.m_attrs)
  }

let trans_field pool f =
  { C.field_name      = CP.lookup_utf8 pool f.CF.f_name
  ; C.field_type      = trans_type (CP.lookup_type pool f.CF.f_desc)
  ; C.field_public    = f.CF.f_flags.AF.f_public
  ; C.field_private   = f.CF.f_flags.AF.f_private
  ; C.field_protected = f.CF.f_flags.AF.f_protected
  ; C.field_static    = f.CF.f_flags.AF.f_static
  ; C.field_final     = f.CF.f_flags.AF.f_final
  ; C.field_volatile  = f.CF.f_flags.AF.f_volatile
  ; C.field_transient = f.CF.f_flags.AF.f_transient
  }

let process_field pool fields f =
  let f = trans_field pool f in
    C.FieldList.update fields (f.C.field_name,f.C.field_type) f

let trans_class cl =
  let pool    = trans_constant_pool cl.CF.pool in
  let fields  = List.fold_left (process_field cl.CF.pool) C.FieldList.empty cl.CF.fields in
  let methods = List.map (trans_method cl.CF.pool) cl.CF.methods in
    { C.preclass_name             = CP.lookup_class_notarray cl.CF.pool cl.CF.this
    ; C.preclass_super_name       = Option.map (CP.lookup_class_notarray cl.CF.pool) cl.CF.super
    ; C.preclass_super_interfaces = List.map (CP.lookup_class_notarray cl.CF.pool) cl.CF.ifcs
    ; C.preclass_public           = cl.CF.flags.AF.c_public
    ; C.preclass_final            = cl.CF.flags.AF.c_final
    ; C.preclass_super            = cl.CF.flags.AF.c_super
    ; C.preclass_interface        = cl.CF.flags.AF.c_interface
    ; C.preclass_abstract         = cl.CF.flags.AF.c_abstract
    ; C.preclass_methods          = methods
    ; C.preclass_fields           = fields
    ; C.preclass_constantpool     = pool
    ; C.preclass_annotation       = trans_class_annot cl.CF.pool cl
    }

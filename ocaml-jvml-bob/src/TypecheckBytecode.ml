(* takes bytecode annotated with stacks and locals and type checks it
*)

module BC = Bytecode
module CD = Classdecl

(* Means that the syntactic sugar for arrays can be used for our
   functional arrays. *)
module Array = FunArray

exception Type_error of string

let ( >> ) x f = f x

let java_lang_String    = Some (Jvmtype.TObject (["java";"lang"], "String"))
let java_lang_Class     = Some (Jvmtype.TObject (["java";"lang"], "Class"))
let java_lang_Throwable = Some (Jvmtype.TObject (["java";"lang"], "Throwable"))

type type_state =
    { locals : CD.vtype_info FunArray.t
    ; stack  : CD.vtype_info list
    }

let contains_uninitialisedthis state =
  let len = FunArray.length state.locals in
  let rec loop i =
    if i = len then false
    else if state.locals.(i) = CD.UninitializedThis_vi then true
    else loop (i+1)
  in
    loop 0

let is_oneword t = match t with
  | CD.Integer_vi
  | CD.Float_vi
  | CD.Null_vi
  | CD.UninitializedThis_vi
  | CD.Uninitialized_vi _
  | CD.Object_vi _ ->
      true
  | CD.Long_vi
  | CD.Double_vi
  | CD.Top_vi ->
      false

let is_twoword t = match t with
  | CD.Integer_vi
  | CD.Float_vi
  | CD.Null_vi
  | CD.UninitializedThis_vi
  | CD.Uninitialized_vi _
  | CD.Object_vi _
  | CD.Top_vi ->
      false
  | CD.Long_vi
  | CD.Double_vi ->
      true

let is_reference t = match t with
  | CD.Uninitialized_vi _
  | CD.UninitializedThis_vi
  | CD.Object_vi _
  | CD.Null_vi ->
      true
  | CD.Top_vi
  | CD.Integer_vi
  | CD.Float_vi
  | CD.Long_vi
  | CD.Double_vi ->
      false

let is_assignable t1 t2 =
  if t1 = t2 then true
  else if t2 = CD.Top_vi then true
  else match t1, t2 with
    | CD.Null_vi,     CD.Object_vi _ -> true
    | CD.Object_vi x, CD.Object_vi y ->
	Printf.printf "FIXME: assuming that %s is a subtype of %s\n" (Jvmtype.string_of_reftype x) (Jvmtype.string_of_reftype y);
	true
    | _,              _              -> false

let frame_assignable f1 f2 =
  if not (List.for_all2 is_assignable f1.stack f2.stack) then
    raise (Type_error "Operand stacks not assignable")
  else
    for i = 0 to Array.length f1.locals - 1 do
      if not (is_assignable f1.locals.(i) f2.locals.(i)) then
	raise (Type_error "Local variables not assignable")
    done
    


let string_of_vtype vt = match vt with
  | CD.Top_vi                  -> "top"
  | CD.Integer_vi              -> "int"
  | CD.Float_vi                -> "float"
  | CD.Long_vi                 -> "long"
  | CD.Double_vi               -> "double"
  | CD.Null_vi                 -> "null"
  | CD.UninitializedThis_vi    -> "uninitializedthis"
  | CD.Object_vi t             -> Jvmtype.string_of_reftype t
  | CD.Uninitialized_vi l      -> "uninitialized(" ^ Label.to_string l ^ ")"

let jtype_to_vtype jtype = match jtype with
  | Jvmtype.TBoolean -> CD.Integer_vi
  | Jvmtype.TChar    -> CD.Integer_vi
  | Jvmtype.TFloat   -> CD.Float_vi
  | Jvmtype.TDouble  -> CD.Double_vi
  | Jvmtype.TByte    -> CD.Integer_vi
  | Jvmtype.TShort   -> CD.Integer_vi
  | Jvmtype.TInt     -> CD.Integer_vi
  | Jvmtype.TLong    -> CD.Long_vi
  | Jvmtype.TRef t   -> CD.Object_vi t

(* FIXME: need to check the spec *)
let sub_type t1 t2 =
  if t1 = t2 then true
  else if t2 = CD.Top_vi then true
  else match t1, t2 with
    | CD.Null_vi,     CD.Object_vi _ -> true
    | CD.Object_vi x, CD.Object_vi y ->
	Printf.printf "FIXME: assuming that %s is a subclass of %s\n" (Jvmtype.string_of_reftype x) (Jvmtype.string_of_reftype y);
	true
    | _,           _           -> false

let sub_type_list l1 l2 = List.for_all2 sub_type l1 l2 (* FIXME: catch Invalid_argument from differing list lengths *)

let check_reference_sub_type t1 t2 = match t1, t2 with
  | None,    _       -> ()
  | _,       None    -> raise (Type_error "Only null is subtype of null")
  | Some t1, Some t2 ->
      Printf.printf "FIXME: assuming that %s is a subclass of %s\n" (Jvmtype.string_of_reftype t1) (Jvmtype.string_of_reftype t2)

(* FIXME: this is certainly wrong *)
let check_progression (stack1, locals1) (stack2, locals2) =
  if not (sub_type_list stack1 stack2 (*&& sub_type_list locals1 locals2*)) then
    raise (Type_error "invalid progression")

let check_is_array t = match t with
  | None
  | Some (Jvmtype.TArray _) -> ()
  | _                       -> raise (Type_error "Expecting an array type")

let pop_reference stack = match stack with
  | []                    -> raise (Type_error "Stack underflow")
  | CD.Null_vi::stack     -> stack, None
  | CD.Object_vi t::stack -> stack, Some t
  | _                     -> raise (Type_error "Expecting reference type on top of stack")

let push_reference stack typ = match typ with
  | None   -> CD.Null_vi::stack
  | Some t -> CD.Object_vi t::stack

let pop expecting stack = match stack with
  | [] -> raise (Type_error "Stack underflow")
  | typ::stack when typ = expecting -> stack
  | _  -> raise (Type_error (Printf.sprintf "Expecting %s on top of stack" (string_of_vtype expecting)))

let pop_double = pop CD.Double_vi
let pop_int    = pop CD.Integer_vi
let pop_float  = pop CD.Float_vi
let pop_long   = pop CD.Long_vi

let pop_1 stack = match stack with
  | CD.Double_vi::_
  | CD.Long_vi::_   -> raise (Type_error "Expecting single-word value on top of stack")
  | t::stack        -> stack, t
  | []              -> raise (Type_error "Stack underflow")

let push typ stack    = typ::stack
let push_double stack = CD.Double_vi::stack
let push_int stack    = CD.Integer_vi::stack
let push_float stack  = CD.Float_vi::stack
let push_long stack   = CD.Long_vi::stack

let obtain_annotations instrs =
  let label_map = Hashtbl.create 14 in
  let process_instr i = match i with
    | BC.Jlabel (label, annotation) ->
	(match annotation#types with
	   | Some types -> Hashtbl.replace label_map label types
	   | None       -> ())
    | _ ->
	()
  in
    List.iter process_instr instrs;
    label_map


let is_twoword typ = match typ with
  | CD.Long_vi | CD.Double_vi -> true
  | _ -> false

let store_oneword idx locals typ =
  assert (not (is_twoword typ));
  let locals = locals.(idx) <- typ in
    if idx > 0 && is_twoword (locals.(idx-1)) then
      locals.(idx-1) <- CD.Top_vi
    else
      locals

let store_twoword idx locals typ =
  assert (is_twoword typ);
  if idx = FunArray.length locals - 1 then
    raise (Type_error (Printf.sprintf "attempt to store a two-word value into last local variable"))
  else
    (locals.(idx) <- typ).(idx+1) <- CD.Top_vi

let load_reference idx locals = match locals.(idx) with
    | CD.Null_vi     -> None
    | CD.Object_vi t -> Some t
    | _              -> raise (Type_error (Printf.sprintf "load_reference: expecting a reference type at lvar %d" idx))

let store_reference idx locals typ = match typ with
  | None -> store_oneword idx locals CD.Null_vi
  | Some t -> store_oneword idx locals (CD.Object_vi t)

let load_double idx locals = match locals.(idx) with
  | CD.Double_vi -> ()
  | _            -> raise (Type_error (Printf.sprintf "load_double: expecting a double at lvar %d" idx))

let store_double idx locals = store_twoword idx locals CD.Double_vi

let load_float idx locals = match locals.(idx) with
  | CD.Float_vi -> ()
  | _           -> raise (Type_error (Printf.sprintf "load_float: expecting a float at lvar %d" idx))

let store_float idx locals = store_oneword idx locals CD.Float_vi

let load_int idx locals = match locals.(idx) with
  | CD.Integer_vi -> ()
  | _             -> raise (Type_error (Printf.sprintf "load_int: expecting an int at lvar %d" idx))

let store_int idx locals = store_oneword idx locals CD.Integer_vi

let load_long idx locals = match locals.(idx) with
  | CD.Long_vi -> ()
  | _          -> raise (Type_error (Printf.sprintf "load_long: expecting a long at lvar %d" idx))

let store_long idx locals = store_twoword idx locals CD.Long_vi

let rec pop_args arg_tys stack =
  let pop_jtype stack ty = match stack with
    | []         -> raise (Type_error "Stack underflow")
    | ty'::stack ->
	if sub_type ty' (jtype_to_vtype ty) then stack else raise (Type_error "Type mismatch")
  in
    List.fold_left pop_jtype stack arg_tys


let typecheck_bytecode instrs (arg_typs, return_type) exception_handlers =
  let annotations = obtain_annotations instrs in

  let lookup_annotation label =
    try Hashtbl.find annotations label
    with Not_found -> raise (Type_error "Dangling label")
  in

  let rec check_exception_handlers handlers locals = match handlers with
    | [] -> ()
    | handler::handlers ->
	let types = lookup_annotation handler.CD.exn_entry in
	  check_progression ([], locals) types;
	  check_exception_handlers handlers locals
  in

  let update_handlers handlers label =
    let handlers = List.filter (fun h -> not (h.CD.exn_end = label)) handlers in
    let new_handlers = List.filter (fun h -> h.CD.exn_start = label) exception_handlers in
      new_handlers @ handlers
  in

  (* FIXME: also want to get a max_stack value out of all this *)

  let rec process_instrs handlers stack_locals_opt instrs = match stack_locals_opt, instrs with
    | None,                 []                               ->
	() (* successful finish *)

    | None,                 BC.Jlabel (label, annot)::instrs ->
	let handlers = update_handlers handlers label in
	  process_instrs handlers (annot#types) instrs

    | None,                 _                                ->
	raise (Type_error "Unreachable instruction")

    | Some (stack, locals), []                               ->
	raise (Type_error "Falling off the end of the code")

    | Some (stack, locals), BC.Jlabel (label, annot)::instrs ->
	let handlers = update_handlers handlers label in
	  (match annot#types with
	     | None                   ->
		 Hashtbl.replace annotations label (stack, locals);
		 process_instrs handlers (Some (stack, locals)) instrs
	     | Some (stack', locals') ->
		 check_progression (stack, locals) (stack', locals');
		 process_instrs handlers (Some (stack', locals')) instrs)

    | Some (stack, locals), BC.Jsconst _::instrs ->
	let stack' = push_reference stack java_lang_String in
	  process_instrs handlers (Some (stack', locals)) instrs

    | Some (stack, locals), BC.Jaaload::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jaastore::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jaconst_null::instrs ->
	let stack' = push_reference stack None in
	  process_instrs handlers (Some (stack', locals)) instrs

    | Some (stack, locals), BC.Jaload i::instrs ->
	let typ = load_reference i locals  in
	let stack' = push_reference stack typ in
	  process_instrs handlers (Some (stack', locals)) instrs

    | Some (stack, locals), BC.Jarraylength::instrs ->
	let stack1, typ = pop_reference stack in
	let _ = check_is_array typ in
	let stack2 = push_int stack1 in
	  process_instrs handlers (Some (stack2, locals)) instrs

    | Some (stack, locals), BC.Jastore i::instrs ->
	let stack', typ = pop_reference stack in
	let locals' = store_reference i locals typ in
	  process_instrs handlers (Some (stack', locals')) instrs

    | Some (stack, locals), BC.Jathrow::instrs ->
	check_exception_handlers handlers locals;
	let stack', typ = pop_reference stack in
	let _ = check_reference_sub_type typ java_lang_Throwable in
	  process_instrs handlers None instrs

    | Some (stack, locals), BC.Jbaload::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jbastore::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jcaload::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jcastore::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jcheckcast ref_typ::instrs ->
	let stack', typ = pop_reference stack in
	let _           = check_reference_sub_type (Some ref_typ) typ in
	let stack''     = push_reference stack' (Some ref_typ) in
	  process_instrs handlers (Some (stack'', locals)) instrs

    | Some (stack, locals), BC.Jclassconst ref_type::instrs ->
	let stack' = push_reference stack java_lang_Class in
	  process_instrs handlers (Some (stack', locals)) instrs

    | Some (stack, locals), BC.Jd2f::instrs ->
	let stack = stack >> pop_double >> push_float in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jd2i::instrs ->
	let stack = stack >> pop_double >> push_float in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jd2l::instrs ->
	let stack = stack >> pop_double >> push_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jdadd::instrs
    | Some (stack, locals), BC.Jdmul::instrs
    | Some (stack, locals), BC.Jdrem::instrs
    | Some (stack, locals), BC.Jddiv::instrs
    | Some (stack, locals), BC.Jdsub::instrs ->
	let stack = stack >> pop_double >> pop_double >> push_double in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jdaload::instrs ->
	assert false

    | Some (stack, locals), BC.Jdastore::instrs ->
	assert false

    | Some (stack, locals), BC.Jdcmpg::instrs
    | Some (stack, locals), BC.Jdcmpl::instrs ->
	let stack = stack >> pop_double >> pop_double >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jdconst _::instrs ->
	let stack1 = stack >> push_double in
	  process_instrs handlers (Some (stack1, locals)) instrs

    | Some (stack, locals), BC.Jdload idx::instrs ->
	let _ = load_double idx locals in
	let stack1 = push_double stack in
	  process_instrs handlers (Some (stack1, locals)) instrs

    | Some (stack, locals), BC.Jdneg::instrs ->
	let stack = stack >> pop_double >> push_double in
	  process_instrs handlers (Some (stack, locals)) instrs
	
    | Some (stack, locals), BC.Jdstore idx::instrs ->
	let stack1 = pop_double stack in
	let locals1 = store_double idx locals in
	  process_instrs handlers (Some (stack1, locals1)) instrs

    | Some (stack, locals), BC.Jdup::instrs ->
	let stack1, typ = pop_1 stack in
	let stack2 = stack1 >> push typ >> push typ in
	  process_instrs handlers (Some (stack2, locals)) instrs

    | Some (stack, locals), BC.Jdup_x1::instrs ->
	let stack, typ1 = pop_1 stack in
	let stack, typ2 = pop_1 stack in
	let stack = stack >> push typ1 >> push typ2 >> push typ1 in
	  process_instrs handlers (Some (stack, locals)) instrs

(*    | Some (stack, locals), BC.Jdup_x2::instrs ->
	let stack, 
*)	    
    (* FIXME: why oh why are the dup instructions so complicated? *)

    | Some (stack, locals), BC.Jf2d::instrs ->
	let stack = stack >> pop_float >> push_double in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jf2i::instrs ->
	let stack = stack >> pop_float >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jf2l::instrs ->
	let stack = stack >> pop_float >> push_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jfadd::instrs
    | Some (stack, locals), BC.Jfmul::instrs
    | Some (stack, locals), BC.Jfdiv::instrs
    | Some (stack, locals), BC.Jfrem::instrs
    | Some (stack, locals), BC.Jfsub::instrs ->
	let stack = stack >> pop_float >> pop_float >> push_float in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jfaload::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jfastore::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jfneg::instrs ->
	let stack = stack >> pop_float >> push_float in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jfload idx::instrs ->
	let _ = load_float idx locals in
	let stack = stack >> push_float in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jfstore idx::instrs ->
	let stack = stack >> pop_float in
	let locals = store_float idx locals in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jfcmpg::instrs
    | Some (stack, locals), BC.Jfcmpl::instrs ->
	let stack = stack >> pop_float >> pop_float >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jfconst _::instrs ->
	let stack = stack >> push_float in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jgetfield (class_name, _, field_typ)::instrs ->
	(* FIXME: extra checks to do with protected fields in the super class *)
	let stack, typ = stack >> pop_reference in
	let _          = check_reference_sub_type typ (Some (Jvmtype.TObject class_name)) in
	let stack      = stack >> push (jtype_to_vtype field_typ) in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jgetstatic (_, _, field_typ)::instrs ->
	let stack      = stack >> push (jtype_to_vtype field_typ) in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jgoto label::instrs ->
	let types = lookup_annotation label in
	let _     = check_progression (stack, locals) types in
	  process_instrs handlers None instrs

    | Some (stack, locals), BC.Ji2b::instrs
    | Some (stack, locals), BC.Ji2c::instrs
    | Some (stack, locals), BC.Ji2s::instrs ->
	let stack = stack >> pop_int >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Ji2d::instrs ->
	let stack = stack >> pop_int >> push_double in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Ji2f::instrs ->
	let stack = stack >> pop_int >> push_float in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Ji2l::instrs ->
	let stack = stack >> pop_int >> push_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jiadd::instrs
    | Some (stack, locals), BC.Jiand::instrs
    | Some (stack, locals), BC.Jimul::instrs
    | Some (stack, locals), BC.Jior::instrs
    | Some (stack, locals), BC.Jirem::instrs
    | Some (stack, locals), BC.Jishl::instrs
    | Some (stack, locals), BC.Jishr::instrs
    | Some (stack, locals), BC.Jisub::instrs
    | Some (stack, locals), BC.Jiushr::instrs
    | Some (stack, locals), BC.Jixor::instrs ->
	let stack = stack >> pop_int >> pop_int >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jidiv::instrs ->
	let _     = check_exception_handlers handlers locals in
	let stack = stack >> pop_int >> pop_int >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jineg::instrs ->
	let stack = stack >> pop_int >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jiaload::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jiastore::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jiconst _::instrs ->
	let stack = stack >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jif_acmpeq label::instrs
    | Some (stack, locals), BC.Jif_acmpne label::instrs ->
	let stack, typ1 = stack >> pop_reference in
	let stack, typ2 = stack >> pop_reference in
	  (* FIXME: do typ1 and typ2 have to be related? *)
	let target_types = lookup_annotation label in
	let _            = check_progression (stack, locals) target_types in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jif_icmpeq label::instrs
    | Some (stack, locals), BC.Jif_icmpne label::instrs
    | Some (stack, locals), BC.Jif_icmplt label::instrs
    | Some (stack, locals), BC.Jif_icmpge label::instrs
    | Some (stack, locals), BC.Jif_icmpgt label::instrs
    | Some (stack, locals), BC.Jif_icmple label::instrs ->
	let stack        = stack >> pop_int >> pop_int in
	let target_types = lookup_annotation label in
	let _            = check_progression (stack, locals) target_types in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jifeq label::instrs
    | Some (stack, locals), BC.Jifne label::instrs
    | Some (stack, locals), BC.Jiflt label::instrs
    | Some (stack, locals), BC.Jifge label::instrs
    | Some (stack, locals), BC.Jifgt label::instrs
    | Some (stack, locals), BC.Jifle label::instrs ->
	let stack        = stack >> pop_int in
	let target_types = lookup_annotation label in
	let _            = check_progression (stack, locals) target_types in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jifnonnull label::instrs
    | Some (stack, locals), BC.Jifnull label::instrs ->
	let stack,typ    = stack >> pop_reference in
	let target_types = lookup_annotation label in
	let _            = check_progression (stack, locals) target_types in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jiinc (idx, _)::instrs ->
	let _      = locals >> load_int idx in
	let locals = locals >> store_int idx in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jiload idx::instrs ->
	let _     = locals >> load_int idx in
	let stack = stack >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jistore idx::instrs ->
	let stack = stack >> pop_int in
	let locals = locals >> store_int idx in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jinstanceof _::instrs ->
	let _        = check_exception_handlers handlers locals in
	let stack, _ = stack >> pop_reference in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jinvokeinterface (class_name, _, (arg_typs, ret_typ))::instrs ->
	let _          = check_exception_handlers handlers locals in
	let stack, typ = stack >> pop_args arg_typs >> pop_reference in
	let _          = check_reference_sub_type typ (Some (Jvmtype.TObject class_name)) in
	let stack      = match ret_typ with None -> stack | Some jtype -> stack >> push (jtype_to_vtype jtype) in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jinvokespecial (class_name, _, (arg_typs, ret_typ))::instrs ->
	(* FIXME: should check that we only invokespecial upon ourselves, or on the super class when it is an initialiser *)
	let _          = check_exception_handlers handlers locals in
	let stack, typ = stack >> pop_args arg_typs >> pop_reference in
	let _          = check_reference_sub_type typ (Some (Jvmtype.TObject class_name)) in
	let stack      = match ret_typ with None -> stack | Some jtype -> stack >> push (jtype_to_vtype jtype) in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jinvokestatic (class_name, _, (arg_typs, ret_typ))::instrs ->
	let _     = check_exception_handlers handlers locals in
	let stack = stack >> pop_args arg_typs in
	let stack = match ret_typ with None -> stack | Some jtype -> stack >> push (jtype_to_vtype jtype) in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jinvokevirtual (class_name, _, (arg_typs, ret_typ))::instrs ->
	let _          = check_exception_handlers handlers locals in
	let stack, typ = stack >> pop_args arg_typs >> pop_reference in
	let _          = check_reference_sub_type typ (Some (Jvmtype.TObject class_name)) in
	let stack      = match ret_typ with None -> stack | Some jtype -> stack >> push (jtype_to_vtype jtype) in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jjsr _::instrs ->
	raise (Type_error "jsr instruction not allowed in type checked bytecode")
    | Some (stack, locals), BC.Jret _::instrs ->
	raise (Type_error "ret instruction not allowed in type checked bytecode")

    | Some (stack, locals), BC.Jl2d::instrs ->
	let stack = stack >> pop_long >> push_double in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jl2f::instrs ->
	let stack = stack >> pop_long >> push_float in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jl2i::instrs ->
	let stack = stack >> pop_long >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jladd::instrs
    | Some (stack, locals), BC.Jland::instrs 
    | Some (stack, locals), BC.Jlmul::instrs 
    | Some (stack, locals), BC.Jlrem::instrs 
    | Some (stack, locals), BC.Jlshl::instrs 
    | Some (stack, locals), BC.Jlshr::instrs 
    | Some (stack, locals), BC.Jlor::instrs 
    | Some (stack, locals), BC.Jlsub::instrs 
    | Some (stack, locals), BC.Jlushr::instrs 
    | Some (stack, locals), BC.Jlxor::instrs ->
	let stack = stack >> pop_long >> pop_long >> push_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jlneg::instrs ->
	let stack = stack >> pop_long >> push_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jlaload::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jlastore::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jlcmp::instrs ->
	let stack = stack >> pop_long >> pop_long >> push_int in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jlconst _::instrs ->
	let stack = stack >> push_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jldiv::instrs ->
	let _     = check_exception_handlers handlers locals in
	let stack = stack >> pop_long >> pop_long >> push_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jlload idx::instrs ->
	let _     = locals >> load_long idx in
	let stack = stack >> pop_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jlstore idx::instrs ->
	let locals = locals >> store_long idx in
	let stack = stack >> push_long in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jmonitorenter::instrs 
    | Some (stack, locals), BC.Jmonitorexit::instrs ->
	let stack, _ = stack >> pop_reference in
	  process_instrs handlers (Some (stack, locals)) instrs

    | Some (stack, locals), BC.Jnew _::instrs ->
	assert false (* FIXME *)

    | Some (stack, locals), BC.Jnop::instrs ->
	process_instrs handlers (Some (stack, locals)) instrs


  in

  let locals = FunArray.create 10 CD.Top_vi in
  let stack = [] in
    process_instrs [] (Some (stack, locals)) instrs (* FIXME: put the argument types in here *)

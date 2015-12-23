module CFI = Ocaml_jvml.ClassfileInput
module JT  = Ocaml_jvml.Jvmtype
open CoqModules
open ExtString
open OptParse

(* Printing of states *)
let rt_val_to_string v = 
  match v with
    | RDT.Coq_rt_int i -> Printf.sprintf "%ld" i
    | RDT.Coq_rt_addr (Some a) -> Printf.sprintf "a(%d)" (Common.Types.int_of_nat (Coqextract.BinPos.Pos.to_nat a))
    | RDT.Coq_rt_addr None -> Printf.sprintf "a(null)"
    | RDT.Coq_rt_long -> Printf.sprintf "l"
    | RDT.Coq_rt_double -> Printf.sprintf "d"
    | RDT.Coq_rt_float -> Printf.sprintf "f"


let rt_val_opt_to_string ov = match ov with
  | None -> "_"
  | Some v -> rt_val_to_string v

let rec stack_to_string l = match l with
  | [] -> ""
  | [v] -> rt_val_to_string v
  | v::l -> (rt_val_to_string v) ^ ", " ^ (stack_to_string l)

let rec lvars_to_string l = match l with
  | [] -> ""
  | [v] -> rt_val_opt_to_string v
  | v::l -> (rt_val_opt_to_string v) ^ ", " ^ (lvars_to_string l)

let print_state state =
  Printf.printf "FS: %d " (List.length state.RDT.state_frame_stack);
  (match state.RDT.state_frame_stack with
     | [] -> print_newline ()
     | f::_ ->
	 Printf.printf " PC: %d; Locals: %s; Stack: %s\n"
	   (Common.Types.int_of_nat f.RDT.frame_pc) (lvars_to_string f.RDT.frame_lvars) (stack_to_string f.RDT.frame_op_stack))

(* Repeating the execution steps of the JVM *)
let rec execstar preclasspool state =
  print_state state;
  match E.exec preclasspool ClassnameSet.empty state with
    | JVM.Coq_cont state' -> execstar preclasspool state'
    | x -> x

let make_descriptor l =
  let rec argdescrip i = if i = 0 then [] else C.Coq_ty_int::(argdescrip (i-1))
  in {C.descriptor_ret_type=Some C.Coq_ty_int; C.descriptor_arg_types=argdescrip l}

let load_class_files preclasses name =
  let rec load_class_files_aux preclasses base package filename =
    match (Unix.stat filename).Unix.st_kind with
      | Unix.S_REG ->
	  if Filename.check_suffix filename ".class" then
	    let class_name = (List.rev package, Filename.chop_suffix (Filename.basename filename) ".class") in
	    let _ = print_string ("Reading " ^ filename ^ " as " ^ (JT.string_of_class class_name) ^ "\n") in
	    let cl = Translate.trans_class (CFI.of_file filename) in
	      CP.Preclasspool.update preclasses class_name cl
	  else
	      preclasses
	| Unix.S_DIR ->
	    let entries = Sys.readdir filename in
	    let new_package = if base then package else Filename.basename filename::package in
	      Array.fold_left
		(fun preclasses nm ->
		   if String.starts_with nm "." then preclasses else load_class_files_aux preclasses false new_package (Filename.concat filename nm))
		preclasses
		entries
	| _ -> preclasses
  in
    load_class_files_aux preclasses true [] name

let exception_to_string s a = match RDT.heap_lookup_class s.RDT.state_classes s.RDT.state_object_heap a with
  | Some t -> JT.string_of_class t
  | None -> "<bad reference>"

let bind ma f s =
  match ma s with
    | JVM.Coq_stop (s,v) -> JVM.Coq_stop (s,v)
    | JVM.Coq_stop_exn (s,e) -> JVM.Coq_stop_exn (s,e)
    | JVM.Coq_cont s -> f s
    | JVM.Coq_wrong -> JVM.Coq_wrong
    | JVM.Coq_undefined -> JVM.Coq_undefined

let load_base_classes preclasspool =
  let rec load_classes classes = function
    | [] -> classes
    | (nm,_)::nms ->
	match R.resolve_class nm nm classes preclasspool with
	  | CP.Coq_load_ok (classes, _) -> load_classes classes nms
	  | CP.Coq_load_err (classes, e) -> failwith ("Failed to load: " ^ (JT.string_of_class nm) ^ " while bootstrapping: "
						     ^ (JT.string_of_class (CP.builtin_exception_to_class_name e)))
  in
  let classes = CP.initial_cert_classpool BIC.j_l_Object_methods BIC.j_l_Object_fields BIC.j_l_Object_pool in
    load_classes classes BuiltinClasses.boot_classes

let parse_arguments () =
  let classpath_opt = StdOpt.str_option ~default:(try Sys.getenv "CLASSPATH" with Not_found -> ".") () in
  let object_limit_opt = StdOpt.int_option () in
  let option_parser = OptParser.make ~description:"A JVM implementation written in Coq" ~usage:"%prog [options] classname methodname [args ...]" () in
  let _ = OptParser.add option_parser
    ~long_name:"classpath"
    ~help:"':' separated list of class files or directories to load classfiles from" classpath_opt in
  let _ = OptParser.add option_parser
    ~long_name:"objlimit"
    ~help:"limit on the number of objects instantiated (default infinity)"
    object_limit_opt in
  let extra = OptParser.parse_argv option_parser in
  let classpaths = String.nsplit (Opt.get classpath_opt) ":" in
  let obj_limit = try RA.Fin (Common.Types.nat_of_int (Opt.get object_limit_opt)) with Opt.No_value -> RA.Inf in
    match extra with
      | class_name::method_name::args ->
	  (classpaths,
	   (match JT.class_of_string class_name with None -> failwith "Invalid class name" | Some x -> x),
	   method_name,
	   obj_limit,
	   List.map (fun s -> Scanf.sscanf s "%ld" (fun i -> i)) args)
      | _ -> begin
	  OptParser.usage option_parser (); exit 1
	end

let load_from_all_paths preclasses classpaths =
  List.fold_left (fun preclasses classpath -> load_class_files preclasses classpath) preclasses classpaths

let string_of_res r =
  RA.Res.fold
    (fun cl cnt s ->
       (BasicsImpl.Classname.to_string cl) ^ ": " ^
       (match cnt with
	  | RA.Inf -> "infinity\n"
	  | RA.Fin i -> string_of_int (Common.Types.int_of_nat i)) ^ "\n")
    r ""

let _ =
  let (classpaths, classname, methname, obj_limit, args) = parse_arguments () in

  let preclasses = load_from_all_paths BuiltinClasses.boot_preclasses classpaths in
  let classes = load_base_classes preclasses in
  let init_state = { RDT.state_frame_stack=[]
		   ; RDT.state_static_fields=RDT.empty_fieldstore classes (RDT.empty_heap classes)
		   ; RDT.state_object_heap=RDT.empty_heap classes
		   ; RDT.state_classes=classes
		   ; RDT.state_res=RA.e
		   ; RDT.state_reslimit=RA.e
		   }
  in
  let args = List.map (fun i -> RDT.Coq_rt_int i) args in
  let descriptor = make_descriptor (List.length args)
  in
    (* Call the method and complete the execution *)
    match bind (E.init preclasses classname methname descriptor args) (execstar preclasses) init_state with
      | JVM.Coq_stop (s,Some v) -> Printf.printf "Stop: %s, objects: %s\n" (rt_val_to_string v) (string_of_res s.RDT.state_res)
      | JVM.Coq_stop (s,None) -> Printf.printf "Stop: no value, objects: %s\n"  (string_of_res s.RDT.state_res)
      | JVM.Coq_stop_exn (s,e) -> Printf.printf "Exception: %s, objects: %s\n" (exception_to_string s e)  (string_of_res s.RDT.state_res)
      | JVM.Coq_wrong -> print_string "wrong\n"
      | JVM.Coq_undefined -> print_string "undefined\n"
      | JVM.Coq_cont _ -> assert false

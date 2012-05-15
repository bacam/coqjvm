open CoqModules

open OptParse
open ExtString

module CFI = Ocaml_jvml.ClassfileInput
module JT  = Ocaml_jvml.Jvmtype

type tocheck =
  | CheckAll
  | CheckOnly of JT.jclass list

let strip_proofs = ref false

let strip_proofs_from cl =
  { cl with C.preclass_annotation = Ann.ProofTable.empty, snd cl.C.preclass_annotation }

let load_class_files preclasses name filterfn =
  let rec load_class_files_aux preclasses base package filename =
    match (Unix.stat filename).Unix.st_kind with
      | Unix.S_REG ->
	  if Filename.check_suffix filename ".class" then
	    let class_name = (List.rev package, Filename.chop_suffix (Filename.basename filename) ".class") in
(*	    let _ = print_string ("Reading " ^ filename ^ " as " ^ (JT.string_of_class class_name) ^ "\n") in*)
            if filterfn class_name then
	      let cl = Translate.trans_class (CFI.of_file filename) in
              let cl = if !strip_proofs then strip_proofs_from cl else cl in
	        CP.Preclasspool.update preclasses class_name cl
            else
              preclasses
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

let parse_arguments () =
  let classpath_opt = StdOpt.str_option ~default:(try Sys.getenv "CLASSPATH" with Not_found -> ".") () in
  let priv_opt = StdOpt.str_option ~default:"" () in
  let res_ref : string list option ref = ref None in
  let res_opt = StdOpt.str_callback (fun s -> res_ref := Some (String.nsplit s " ")) in
  let printvcs_opt = StdOpt.store_true () in
  let option_parser = OptParser.make ~description:"A certificate verifier written in Coq" ~usage:"%prog [options] classname [methodname]" () in
  let _ = OptParser.add option_parser
    ~long_name:"classpath"
    ~help:"':' separated list of class files or directories to load classfiles from" classpath_opt in
  let _ = OptParser.add option_parser
    ~long_name:"priv"
    ~help:"' ' separated list of class names which are privileged" priv_opt in
  let _ = OptParser.add option_parser
    ~long_name:"resources"
    ~help:"' ' separated list of class names which are considered resources" res_opt in
  let _ = OptParser.add option_parser
    ~long_name:"print-vcs"
    ~help:"Print the VCs (by ignoring any proofs present)" printvcs_opt in
  let extra = OptParser.parse_argv option_parser in
  let classpaths = String.nsplit (Opt.get classpath_opt) ":" in
  let privclasses = String.nsplit (Opt.get priv_opt) " " in
  let _ = strip_proofs := Opt.get printvcs_opt in
    match extra with
      | [] -> (classpaths, privclasses, !res_ref, CheckAll)
      | class_names ->
          let classes =
            List.map (fun class_name ->
                        match JT.class_of_string class_name with None -> failwith "Invalid class name" | Some x -> x) class_names in
	  (classpaths, privclasses, !res_ref, CheckOnly classes)

let load_from_all_paths preclasses classpaths filterfn =
  List.fold_left (fun preclasses classpath -> load_class_files preclasses classpath filterfn) preclasses classpaths

let print_vcs vcs =
  if !strip_proofs
  then print_endline "Verification conditions required:"
  else print_endline "No proofs for the following verification conditions:";
  List.iter (function ((f,f'), srcs) ->
    print_endline (String.concat ", "
		     (List.map
                        (function VCs.Coq_vc_spec (cls,mth,pc) ->
			     (JT.string_of_class cls) ^ "." ^ mth ^ "@" ^ (Common.MLStringsImpl.mlstring_of_nat pc)
                           | VCs.Coq_vc_override (cls,mth) -> (JT.string_of_class cls) ^ "@" ^ mth) srcs));
    print_endline ("  " ^ ResILLBase.SYN.string_of_formula f ^ " entails " ^
		          ResILLBase.SYN.string_of_formula f')) vcs

let check_loaded preclasses = function
  | CheckAll -> ()
  | CheckOnly l ->
      match List.filter (fun x -> Option.is_none (CP.Preclasspool.lookup preclasses x)) l with
        | []  -> ()
        | [x] -> print_endline ("Unable to find class: " ^ JT.string_of_class x)
        | l'  -> print_endline ("Unable to find classes: " ^ String.concat ", " (List.map JT.string_of_class l'))

let _ =
  let (classpaths, privclasses, resclasses, classestocheck) = parse_arguments () in
  let _ = Option.may (fun l ->
			let l' = List.map TranslateTools.class_of_string l in
			  Filter.f0 := fun c -> List.mem c l') resclasses in
  let classfilter =
    match classestocheck with
      | CheckAll -> (fun _ -> true)
      | CheckOnly l -> (fun x -> List.mem x l)
  in
  let preclasses = load_from_all_paths BuiltinClasses.boot_preclasses classpaths classfilter in
  let _ = check_loaded preclasses classestocheck in
  let specs = ResChecker.OverrideChecker.ClassTable.add BasicsImpl.java_lang_Object ResChecker.OverrideChecker.SpecTable.empty ResChecker.OverrideChecker.ClassTable.empty in
  let privset = List.fold_left (fun s c -> ClassnameSet.add (TranslateTools.class_of_string c) s) ClassnameSet.empty privclasses in

    match ResChecker.check_preclasses preclasses privset specs with
      | Coqextract.ErrorMonad.Val [] -> print_endline "preclass verification ok"
      | Coqextract.ErrorMonad.Val vcs -> print_vcs vcs
      | Coqextract.ErrorMonad.Err msg -> print_endline ("Verification failed: " ^ msg)


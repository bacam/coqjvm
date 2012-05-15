open CoqModules
open TranslateTools
open ResILLBase.SYN

let trivial_code_annot = Cert.Cert.empty
let trivial_class_annot =
  (Ann.ProofTable.update Ann.ProofTable.empty (Coq_f_i,Coq_f_i) ILL.Coq_t_i_intro, Ann.ConstantPoolAdditional.empty)

  module JT = Ocaml_jvml.Jvmtype
  module LB = Ocaml_jvml.LowlevelBytecode
  module CP = Ocaml_jvml.Constpool
  module CF = Ocaml_jvml.Classfile
  module AF = Ocaml_jvml.AccessFlags

let split s =
  let rec next i l =
    try
      let j = String.index_from s i ';' in
      let k =
	try String.index_from s (j+1) ';'
	with Not_found -> String.length s
      in
      next (k+1) ((String.sub s i (j-i), String.sub s (j+1) (k-j-1))::l)
    with
	Not_found | Invalid_argument _ -> List.rev l
  in next 0 []


let find_attr pool s l =
  match List.find (fun (CF.Attribute (cpid,_)) -> CP.lookup_utf8 pool cpid = s) l with
    | CF.Attribute (_, CF.Attr a) -> a
    | _ -> failwith ("Attribute " ^ s ^ " was of the wrong type")


let parse_formula s =
  let lexer = Lexing.from_string s in
  let absyn = Ill_parser.full_formula Ill_lexer.token lexer in
    ILL_Translate.formula_to_coq absyn

let parse_specification spec =
  let lexer = Lexing.from_string spec in
  let (pre, ensures, ex_ensures) = Ill_parser.specification Ill_lexer.token lexer in
    (ILL_Translate.formula_to_coq pre,
     ILL_Translate.formula_to_coq ensures,
     ILL_Translate.formula_to_coq ex_ensures)

let poor_triplet (a,b,c) = ((a,b),c)



let trans_ptentry m = function (formulae,term) ->
  let lexerf = Lexing.from_string formulae in
  let (ass,ens) = Ill_parser.formula_pair Ill_lexer.token lexerf in
  let lexerp = Lexing.from_string term in
  let prf = Ill_parser.full_term Ill_lexer.token lexerp in
    Ann.ProofTable.update m
      ((ILL_Translate.formula_to_coq ass,ILL_Translate.formula_to_coq ens))
      (ILL_Translate.term_to_coq [] ["x"] prf)

let trans_cpae_entry cpa (id,entry) =
  let update v =
    Ann.ConstantPoolAdditional.update cpa (CP.index_of_int (int_of_string id)) v
  in
  let spec () =
    parse_specification (String.sub entry 2 ((String.length entry)-2))
  in
  match String.sub entry 0 2 with
    | "sm" -> let (p,e,x) = spec () in update (Ann.Coq_cpae_static_method (p,e,x))
    | "sf" -> update Ann.Coq_cpae_static_field
    | "ic" -> update Ann.Coq_cpae_instantiable_class
    | "if" -> update Ann.Coq_cpae_instance_field
    | "im" -> let (p,e,x) = spec () in update (Ann.Coq_cpae_instance_method (p,e,x))
    | "fm" -> let (p,e,x) = spec () in update (Ann.Coq_cpae_interface_method (p,e,x))
    | "is" -> let (p,e,x) = spec () in update (Ann.Coq_cpae_instance_special_method (p,e,x))
    | "cr" -> update Ann.Coq_cpae_classref
    | x -> failwith ("Unrecogised CPA entry: " ^ x)


let trans_code_annot pool pos_table attrs =
  try
    let certanno = find_attr pool "uk.ac.ed.inf.request.Certificate" attrs in
    let certpairs = split certanno in
      List.fold_left (fun cert (pc, formula) ->
			Cert.Cert.update cert
			  (Common.Types.nat_of_int (pos_table.(int_of_string pc)))
			  (parse_formula formula)) Cert.Cert.empty certpairs
  with Not_found -> trivial_code_annot

let trans_method_annot pool m =
  let methspec = try
    let s = find_attr pool "uk.ac.ed.inf.request.Spec" m.CF.m_attrs in
      poor_triplet (parse_specification s)
  with Not_found -> Ann.trivial_method_annotation.Ann.method_spec in
  let grants = try
    let s = find_attr pool "uk.ac.ed.inf.request.Grants" m.CF.m_attrs in
    Some (breakup_res s)
  with Not_found -> Ann.trivial_method_annotation.Ann.grants in
    { Ann.method_spec = methspec; Ann.grants = grants }

let trans_class_annot pool cl =
  try
    let prooftable =
      try
	let ptattr = find_attr pool "uk.ac.ed.inf.request.ProofTable" cl.CF.attrs in
          List.fold_left trans_ptentry Ann.ProofTable.empty (split ptattr)
      with Not_found -> Ann.ProofTable.empty
    in
    let cpa =
      try
	let cpaattr = find_attr pool "uk.ac.ed.inf.request.ConstantPoolAdditional" cl.CF.attrs in
	  List.fold_left trans_cpae_entry Ann.ConstantPoolAdditional.empty
	    (split cpaattr)
      with Not_found -> Ann.ConstantPoolAdditional.empty
    in (prooftable, cpa)
  with Not_found -> trivial_class_annot

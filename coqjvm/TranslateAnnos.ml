open CoqModules
open Coqextract
open TranslateTools

module CF = Ocaml_jvml.Classfile

let trivial_code_annot = ()
let trivial_class_annot = ()
let trans_code_annot pool _ _ = ()
let trans_method_annot pool m = 
  try
    let grants = find_attr pool "uk.ac.ed.inf.request.Grants" m.CF.m_attrs in
    Some (breakup_res grants)
  with Not_found -> EA.trivial_method_annotation
let trans_class_annot pool c = ()

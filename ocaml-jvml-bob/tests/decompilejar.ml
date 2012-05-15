open ExtString
open Ocaml_jvml

module CD = Classdecl

let count = ref 0
let entries_done = ref 0

let lastlen = ref 0

(*exception Difference of string

let triv_compare s a b = if a <> b then raise (Difference (s ^ ": difference"))

let rec compare_list s f l1 l2 = match l1, l2 with
  | [],    []    -> ()
  | [],    _     -> raise (Difference (s ^ ": list 2 has more members"))
  | _,     []    -> raise (Difference (s ^ ": list 1 has more members"))
  | a::l1, b::l2 -> f a b; compare_list s f l1 l2

let compare_code c1 c2 =
  if c1.CD.stack <> c2.CD.stack then raise (Difference "stacks differ");
  if c1.CD.locals <> c2.CD.locals then raise (Difference "locals differ");
  if c1.CD.code <> c2.CD.code then (print_newline (); Bytecode.printInstrs c1.CD.code; print_newline (); Bytecode.printInstrs c2.CD.code; raise (Difference "instructions differ"));
  if c1.CD.hdls <> c2.CD.hdls then raise (Difference "handlers differ");
  if c1.CD.code_attrs <> c2.CD.code_attrs then raise (Difference "attrs differ")

let compare_attribute a1 a2 = match a1, a2 with
  | CD.CONSTVAL c1,      CD.CONSTVAL c2 -> if c1 <> c2 then raise (Difference "constant values different")
  | CD.CODE c1,          CD.CODE c2     -> compare_code c1 c2
  | CD.EXNS e1,          CD.EXNS e2     -> if e1 <> e2 then raise (Difference "exceptions different")
  | a1,                  a2             -> if a1 <> a2 then raise (Difference "attrs differ")

let compare_methods m1 m2 =
  let n = m1.CD.md_name ^ "/" ^ m2.CD.md_name in
    if m1.CD.md_flags <> m2.CD.md_flags then raise (Difference (Printf.sprintf "%s: flags differ" n));
    if m1.CD.md_name <> m2.CD.md_name then raise (Difference (Printf.sprintf "%s: namess differ" n));
    if m1.CD.md_sig <> m2.CD.md_sig then raise (Difference (Printf.sprintf "%s: sigs differ" n));
    compare_list "method attrs" (compare_attribute) m1.CD.md_attrs m2.CD.md_attrs

let compare_decls cd1 cd2 =
  if cd1.CD.major_minor <> cd2.CD.major_minor then raise (Difference "Major, minor numbers differ");
  if cd1.CD.flags <> cd2.CD.flags then raise (Difference "Flags differ");
  if cd1.CD.this <> cd2.CD.this then raise (Difference "'this' differs");
  if cd1.CD.super <> cd2.CD.super then raise (Difference "'super' differs");
  if cd1.CD.interfaces <> cd2.CD.interfaces then raise (Difference "'interfaces' differ");
  if cd1.CD.fields <> cd2.CD.fields then raise (Difference "'fields' differ");
  compare_list "methods" compare_methods cd1.CD.methods cd2.CD.methods;
  if cd1.CD.attrs <> cd2.CD.attrs then raise (Difference "'attrs' differ")
*)

let test_entry file entry =
  if not entry.Zipfile.e_is_directory && String.ends_with entry.Zipfile.e_filename ".class" then
    (* print out what we are doing *)
    let len   = String.length entry.Zipfile.e_filename + 25 in
    let wipe  = String.make (max 0 (!lastlen - len)) ' ' in
    let ()    = lastlen := len in
    let ()    = Printf.printf "% 6d/% 5d : Processing %s%s\r" !entries_done !count entry.Zipfile.e_filename wipe in

    (* do it *)
    let data  = Zipfile.read_entry file entry in
    let cf    = ClassfileInput.read_classfile (IO.input_string data) in
    let cd    = Decompile.decompile cf in
    let _     = Compile.compile cd in
    (*let cd'   = Decompile.decompile cf in*) (* FIXME: we would compare them here, but the presence of 'nan' breaks the comparisons *)
      (*compare_decls cd cd';*)
      incr entries_done

let _ =
  let filename = Sys.argv.(1) in
  let jarfile  = Zipfile.open_in filename in
    count := Zipfile.num_entries jarfile;
    (try
       Zipfile.iter jarfile (test_entry jarfile)
     with e -> print_newline (); raise e);
    print_newline ()

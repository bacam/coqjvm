open ExtString
open Ocaml_jvml

let count = ref 0
let entries_done = ref 0

let lastlen = ref 0

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
    let out   = IO.output_string () in
    let _     = ClassfileOutput.write_classfile out cf in
    let data' = IO.close_out out in
      if data <> data' then failwith "Written classfile differs from original";
      incr entries_done

let _ =
  let filename = Sys.argv.(1) in
  let jarfile  = Zipfile.open_in filename in
    count := Zipfile.num_entries jarfile;
    (try
       Zipfile.iter jarfile (test_entry jarfile)
     with e -> print_newline (); raise e);
    print_newline ()

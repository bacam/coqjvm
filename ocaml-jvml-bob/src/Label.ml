(* Label.ml
 *
 * Kenneth MacKenzie
 * May 2006
 *)

(* idea for the future: named labels so that pretty printing can look
   prettier. Need to make sure that each label for a given generator is
   uniquely named (nicely) *)

type label  = int
type labels = int ref

let to_string n = "label" ^ string_of_int n

(*let of_int n = LBL (n, ())
  let to_int (LBL (n,_)) = n (* Inserted - kwxm *)*)

let label_generator () = ref 0

let new_label generator =
  let n = !generator in
    incr generator;
    n

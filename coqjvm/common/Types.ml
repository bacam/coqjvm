(* These are types which are used in the coq developement, and in ocaml files
   which the coq extracted ocaml relies on.  A separate definition of these is
   required because ocaml does not allow mutually dependent files. *)

type nat = O | S of nat

let rec int_of_nat n = match n with O -> 0 | S n -> 1 + int_of_nat n
let rec nat_of_int n = match n with 0 -> O | n -> S (nat_of_int (n-1))
let rec nat_of_int32 n =
  if compare n Int32.zero = 0 then O
  else S (nat_of_int32 (Int32.sub n Int32.one))

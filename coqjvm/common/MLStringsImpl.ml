open Types

(* Not using these for now
let mlstring_of_string s =
  let rec addlength n = function
    | String.EmptyString -> n
    | String.String (_,s') -> addlength (n+1) s'
  in
  let l = addlength 0 s in
  let r = String.create l in
  let rec set n = function
    | String.EmptyString -> r
    | String.String (c,s') -> r.[n] <- c; set (n+1) s'
  in set 0 s
*)

let mlstring_of_nat n =
  string_of_int (int_of_nat n)

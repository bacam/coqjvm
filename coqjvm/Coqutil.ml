open Coqextract

let rec z_of_int n =
  let rec pos_of_int n = if n = 1 then BinPos.Coq_xH else BinPos.coq_Psucc (pos_of_int (n-1)) in
    if n = 0 then BinInt.Z0
    else if n < 0 then BinInt.Zneg (pos_of_int (-n))
    else BinInt.Zpos (pos_of_int n)

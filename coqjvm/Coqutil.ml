open Coqextract

let rec z_of_int n =
  let rec pos_of_int n = if n = 1 then BinNums.Coq_xH else BinPos.Pos.succ (pos_of_int (n-1)) in
    if n = 0 then BinNums.Z0
    else if n < 0 then BinNums.Zneg (pos_of_int (-n))
    else BinNums.Zpos (pos_of_int n)

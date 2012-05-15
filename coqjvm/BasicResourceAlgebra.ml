module A = struct
  module B = BasicsImpl

  type res = Inf | Fin of int

  let leq_dec i1 i2 = match i1, i2 with
    | Inf,    Inf    -> true
    | Inf,    Fin _  -> false
    | Fin _,  Inf    -> true
    | Fin i1, Fin i2 -> i1 <= i2

  let combine i1 i2 = match i1, i2 with
    | Inf,    Inf    -> Inf
    | Inf,    Fin _  -> Inf
    | Fin _,  Inf    -> Inf
    | Fin i1, Fin i2 -> Fin (i1 + i2)

  let e = Fin 0

  let bang i = Inf (* FIXME: this is wrong: really need integers + positive infinity *)

  let r_new _ = Fin 1

  let string_of_res i = match i with
    | Inf -> "infinity"
    | Fin i -> string_of_int i
end


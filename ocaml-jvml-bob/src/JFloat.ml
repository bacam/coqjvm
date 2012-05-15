type t = int32

let of_float = Int32.bits_of_float
let to_float = Int32.float_of_bits
let read = IO.BigEndian.read_real_i32
let write = IO.BigEndian.write_real_i32

let one = Int32.bits_of_float 1.0
let zero = Int32.bits_of_float 0.0
let two = Int32.bits_of_float 2.0


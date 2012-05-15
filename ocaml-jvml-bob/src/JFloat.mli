(** 32bit single precision floating point numbers for Java [.class] files *)

(**{1 32bit Single-Precision Floating Point Numbers}

   This modules provides minimal facilities for representing 32bit
   floating point values in memory and reading and writing them from
   byte streams.
*)

(** The type of 32bit floating point numbers *)
type t

(** Convert an O'Caml 64bit double precision floating point number to
    the internal representation. May involve loss of precision. *)
val of_float : float -> t

(** Convert the internal representation to an O'Caml double precision
floating point number. *)
val to_float : t -> float

(** Read a 32bit single-precision floating point number from the input
    in big-endian format *)
val read : IO.input -> t

(** Write a 32bit single-precision floating point number to the output
    in big-endian format *)
val write : 'a IO.output -> t -> unit

(** Constant value 1.0. Equal to {!JFloat.of_float} [1.0]. *)
val one  : t

(** Constant value 0.0. Equal to {!JFloat.of_float} [0.0]. *)
val zero : t

(** Constant value 2.0. Equal to {!JFloat.of_float} [2.0]. *)
val two  : t

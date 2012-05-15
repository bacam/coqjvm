(** Functional arrays based on maps *)

(**{1 Functional Arrays}*)

(** Type of functional arrays, parameterised by the type of
    elements. *)
type +'a t

(** Exception thrown when there is a *)
exception Out_of_bounds of int * int

  (** [create len v] creates a new array of length [len] filled with [v]
      at every element. *)
val create : int -> 'a -> 'a t

(** Returns the length of an array. *)
val length : 'a t -> int

(** Retrieves a value from the array at a given index. *)
val get : 'a t -> int -> 'a

(** Updates the array with the value at the given index. Returns the
    new array. The old array is untouched. *)
val set : 'a t -> int -> 'a -> 'a t

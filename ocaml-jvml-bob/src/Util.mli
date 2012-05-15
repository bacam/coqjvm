(** Utility types and functions *)

(**{1 Utility types and functions} *)

(** Extensions to the Extlib [IO] module. *)
module IO : sig
    (** [limited_input n input] returns a handle that raises
	[IO.No_more_input] after reading [n] bytes. *)
  val limited_input : int -> IO.input -> IO.input
end

(** A little module for formatting lists in strings *)
module ListBuilder : sig
  type t
  val create   : string -> t
  val add      : t -> string -> unit
  val contents : t -> string
end

(** Repeat a function a fixed number of times. *)
val repeat : int -> (unit -> 'a) -> unit

(** Repeat a function a fixed number of times, collecting the results
    into a list. *)
val repeat_collect : int -> (unit -> 'a) -> 'a list

(** Repeatedly execute a function until it returns [None], collecting
    all the results into a list. *)
val repeat_until_None : (unit -> 'a option) -> 'a list

(** [find_first f l] finds the first element of [l] such that [f]
    returns [Some x] on that element. *)
val find_first : ('a -> 'b option) -> 'a list -> 'b option

(** [lookahead_lexer token lexbuf] creates an object that reads tokens
from [lexbuf] by calling [token lexbuf]. The current token can be
accessed by the method [tok], the next token is read using the method
[advance] and the position of the current token is given by [pos]. *)
val lookahead_lexer : (Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> < tok : 'a; advance : unit -> unit; pos : Lexing.position * Lexing.position >

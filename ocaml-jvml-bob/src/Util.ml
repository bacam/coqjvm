module IO = struct
  let limited_input limit original_input =
    let counter = ref 0 in
    let read () =
      if !counter = limit then raise IO.No_more_input;
      incr counter;
      IO.read original_input
    in
    let input buffer start maximum =
      if !counter = limit then raise IO.No_more_input;
      let maximum' = min maximum (limit - !counter) in
      let read_count = IO.input original_input buffer start maximum' in
	counter := !counter + read_count;
	read_count
    in
    let close () =
      IO.close_in original_input
    in
      IO.create_in read input close
end

module ListBuilder : sig
  type t
  val create   : string -> t
  val add      : t -> string -> unit
  val contents : t -> string
end = struct
  type t =
      { mutable empty  : bool
      ;         buffer : Buffer.t
      ;         delim  : string
      }

  let create delim =
    { empty  = true
    ; buffer = Buffer.create 10
    ; delim  = delim
    }

  let add builder item =
    if not (builder.empty) then
      Buffer.add_string builder.buffer builder.delim
    else
      builder.empty <- false;
    Buffer.add_string builder.buffer item

  let contents builder =
    Buffer.contents builder.buffer
end

(* Miscellaneous *)

let rec repeat n f = match n with
  | 0 -> ()
  | n -> f (); repeat (n-1) f

let repeat_collect n f =
  let rec loop n acc = match n with
    | 0 -> List.rev acc
    | n -> loop (n-1) (f ()::acc)
  in loop n []

let repeat_until_None f =
  let rec loop l = match f () with
    | None   -> List.rev l
    | Some x -> loop (x::l)
  in
    loop []

let rec find_first f l = match l with
  | []   -> None
  | x::l -> (match f x with
	       | Some a -> Some a
	       | None   -> find_first f l)

let lookahead_lexer token lexbuf =
object
  val mutable current_token = token lexbuf
  method tok        = current_token
  method advance () = current_token <- token lexbuf
  method pos        = (lexbuf.Lexing.lex_curr_p, lexbuf.Lexing.lex_curr_p)
end

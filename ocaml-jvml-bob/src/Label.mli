(** Abstract type of labels for high-level bytecode. *)

type label
type labels

val to_string : label -> string

val label_generator : unit -> labels

val new_label : labels -> label

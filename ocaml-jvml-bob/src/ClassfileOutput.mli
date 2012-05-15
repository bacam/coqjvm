(** Writes {!Classfile.class_file} structures to byte streams in JVM [.class] format *)

(**{1 Class file Output} *)

(** Exception thrown when there is an error during class file
    output. The string gives the reason *)
exception ClassfileOutputError of string

(** Writes a class file to a byte stream. 

    @raise ClassfileOutput.ClassfileOutputError if the class file structure is invalid.
*)
val write_classfile : 'a IO.output -> Classfile.class_file -> unit

(** Writes a class file to a named file on disk. *)
val to_file : Classfile.class_file -> string -> unit

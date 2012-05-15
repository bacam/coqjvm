(** Reads in {!Classfile.class_file} values from a stream of bytes
    representing a JVM [.class] file *)

(**{1 Class file Input}

   
*)

(** Exception thrown by {!ClassfileInput.read_classfile} when the
    input is invalid. The string argument gives the reason. *)
exception ClassfileInputError of string

(** Read a class file structure from the input. It stops reading at
    the intrinsic end of the class file structure. It does not check
    that there is no more input. If there is a problem reading the
    input then {!ClassfileInput.ClassfileInputError} is raised. {b
    FIXME}: and some other exceptions: wrap these up? *)
val read_classfile : IO.input -> Classfile.class_file

(** Wrapper function that opens a file and reads in a class file
    structure using {!ClassfileInput.read_classfile} *)
val of_file : string -> Classfile.class_file

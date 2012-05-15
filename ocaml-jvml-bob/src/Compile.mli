(** Compilation of high-level class representations to low-level *)

(**{1 Compilation of high-level class representations to low-level} *)

(** Exception thrown for errors occuring during compilation. *)
exception CompileError of string

(**{2 Compilation of custom attributes} *)

(** Type of records containing callbacks for compiling custom
    attributes in {!Classdecl.class_decl} values. Each compiler takes
    the custom datatype and a {!Constpool.builder} object and should
    produce a pair [(name,data)] of the attribute name and the
    attribute's binary data. The {!Constpool.builder} object supplied
    is being used to construct the constant pool for the compiled
    class. The compiler for code attributes is also given a mapping
    from {!Label.label} points in the bytecode to actual code
    offsets. *)
type ('f,'m,'c,'cl) attribute_compilers =
    { compile_field_attribute  : 'f -> Constpool.builder -> (string * string) list (** compile field attributes *)
    ; compile_method_attribute : 'm -> Constpool.builder -> (string * string) list (** compile method attributes *)
    ; compile_code_attribute   : 'c -> Constpool.builder -> (Label.label, int) Hashtbl.t -> (string * string) list (** compile code attributes *)
    ; compile_class_attribute  : 'cl -> Constpool.builder -> (string * string) list (** compile class attributes *)
    }

(** Compilers for generic attributes that are already a pair of name
    and binary data. *)
val null_attribute_compilers : (unit, unit, unit, unit) attribute_compilers

(**{2 Compilation} *)

(** Compiles a high-level !Classdecl.class_decl value to a low-level
    {!Classfile.class_file} value, using a supplied set of callbacks
    to compile custom attributes in the high-level declaration. *)
val compile : ('f,'m,'c,'cl) Classdecl.class_decl -> ('f,'m,'c,'cl) attribute_compilers -> Classfile.class_file

(** Compiles directly to a file on disk. Invokes {!Compile.compile} to
    do the actual compilation. *)
val to_file : ('f,'m,'c,'cl) Classdecl.class_decl -> ('f,'m,'c,'cl) attribute_compilers -> string -> unit

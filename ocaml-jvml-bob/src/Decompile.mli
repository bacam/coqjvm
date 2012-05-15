(** Decompilation of low-level class representations to high-level *)

(**{1 Decompilation of [.class] files}

   This module contains functions to translate the low-level
   {!Classfile.class_file} representation to the high-level
   {!Classdecl.class_decl} high-level representation.
*)

(**{2 Exception} *)

(** Exception thrown if there is a problem during decompilation. *)
exception DecompileError of string

(**{2 Decompilation of annotations} *)

(*val decompile_element : Constpool.pool -> Classfile.element -> Classdecl.element

val decompile_element_pair :
  Constpool.pool -> Constpool.index * Classfile.element -> string * Classdecl.element*)

(** Decompile a single annotation, given a constant pool to look-up
    the references. *)
val decompile_annotation : Constpool.pool -> Classfile.annotation -> Classdecl.annotation

(**{2 Decompilation of custom attributes} *)

(** Type of records containing callbacks for decompiling custom
    attributes into {!Classdecl.class_decl} values. Each decompiler
    takes a pair [(name,data)] of the attribute name and the
    attribute's binary data along with the class pool and should
    produce a value of the custom datatype.  The decompiler for code
    attributes is also given a mapping from code offsets to
    {!Label.label} points in the bytecode. FIXME: update *)
type ('f,'m,'c,'cl) attribute_decompilers =
    { empty_field_attribute      : 'f
    ; empty_method_attribute     : 'm
    ; empty_code_attribute       : 'c
    ; empty_class_attribute      : 'cl
    ; decompile_field_attribute  : 'f -> string * string -> Constpool.pool -> 'f option (** decompile field attributes *)
    ; decompile_method_attribute : 'm -> string * string -> Constpool.pool -> 'm option (** decompile method attributes *)
    ; decompile_code_attribute   : 'c -> string * string -> Constpool.pool -> (int -> Label.label) -> 'c option (** decompile code attributes *)
    ; decompile_class_attribute  : 'cl -> string * string -> Constpool.pool -> 'cl option (** decompile class attributes *)
    }

(** Decompilers for empty custom attributes. *)
val null_attribute_decompilers : (unit, unit, unit, unit) attribute_decompilers

(**{2 Decompilation of files} *)

(** Decompile a lowlevel {!Classfile.class_file} to a high-level
    {!Classdecl.class_decl}, using the supplied generic attribute decompilers. *)
val decompile : Classfile.class_file -> ('f,'m,'c,'cl) attribute_decompilers -> ('f,'m,'c,'cl) Classdecl.class_decl

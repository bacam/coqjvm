(** Representation, writing and parsing of Java types for the JVM *)

(**{1 Representation, writing and parsing of Java types for the JVM}

   This module contains types for representing Java types and
   functions for reading and writing their JVM representations. *)

(**{2 Types} *)

(** Type of fully qualified class names. *)
type jclass = string list * string

(** Reference types *)
type jref_type =
  | TObject of jclass
  | TArray of jtype

(** Primitive and reference types. *)
and jtype =
  | TBoolean
  | TChar
  | TFloat
  | TDouble
  | TByte
  | TShort
  | TInt
  | TLong
  | TRef of jref_type

(** Type of method signatures: list of argument types and an optional
    return type. *)
type methodsig = jtype list * jtype option

(**{2 Writing} *)

(** Return a string containing the JVM internal form of a class
    name. Inverse to {!Jvmtype.class_of_string}. *)
val string_of_class : jclass -> string

(** Return a string containing the JVM internal form for a
    type. Inverse to {!Jvmtype.type_of_string}. *)
val string_of_type : jtype -> string

(** Return a string containing the JVM internal form for a reference
    type. Note that [string_of_reftype x] is different to
    {!Jvmtype.string_of_type} [(TRef x)]: class names are not of the
    form [Lclassname;]. Inverse to {!Jvmtype.reftype_of_string}. *)
val string_of_reftype : jref_type -> string

(** Return a string containing the JVM internal form of a method
    signature. Inverse to {!Jvmtype.methodsig_of_string}. *)
val string_of_methodsig : methodsig -> string

(**{2 Reading} *)

(** Parse a JVM internal form of a class name. Returns [None] if
    parsing fails. Inverse to {!Jvmtype.string_of_class}. *)
val class_of_string : string -> jclass option

(** Parse a JVM internal form of a type. Returns [None] if
    parsing fails. Inverse to {!Jvmtype.string_of_type}. *)
val type_of_string : string -> jtype option

(** Parse a JVM internal form of a reference type. Returns [None] if
    parsing fails. Inverse to {!Jvmtype.string_of_type}. *)
val reftype_of_string : string -> jref_type option

(** Parse a JVM internal form of a method signature. Returns [None] if
    parsing fails. Inverse to {!Jvmtype.string_of_methodsig}. *)
val methodsig_of_string : string -> methodsig option

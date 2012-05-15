(** Special handling of selected attributes. *)

(**{1 Special handling of selected attributes} *)

(**{2 Text parsing and formatting} *)

(** In addition to the {!Compile.attribute_compilers} and
    {!Decompile.attribute_decompilers}, we also wish to define parsers and
    formatters to deal with attributes as plain text. *)

type ('f,'m,'c,'cl) attribute_parsers = {
  (* NB: at the time of writing the assembler doesn't handle field attributes. *)
  parse_field_attribute  : string * string -> 'f;
  parse_method_attribute : string * string -> 'm;
  parse_code_attribute   : string * string -> (string -> Label.label) -> 'c;
  parse_class_attribute  : string * string -> 'cl;
}

type ('f,'m,'c,'cl) attribute_formatters = {
  format_field_attribute  : 'f -> string * string;
  format_method_attribute : 'm -> string * string;
  format_code_attribute   : (Label.label -> string) -> 'c -> string * string;
  format_class_attribute  : 'cl -> string * string;
}

(**{2 Handling of attributes for the resource verifier} *)

(** For the Constant Pool Additional attributes we need to store enough
    information to find the index of the corresponding constant pool
    entry. The methods have an extra string to hold the
    specification. *)
type cpaentry =
  | CPAE_static_method of Jvmtype.jref_type * string * Jvmtype.methodsig * string
  | CPAE_static_field of Jvmtype.jclass * string * Jvmtype.jtype
  | CPAE_instantiable_class of Jvmtype.jref_type
  | CPAE_instance_field of Jvmtype.jclass * string * Jvmtype.jtype
  | CPAE_instance_method of Jvmtype.jref_type * string * Jvmtype.methodsig * string
  | CPAE_instance_special_method of Jvmtype.jref_type * string * Jvmtype.methodsig * string
  | CPAE_classref of Jvmtype.jref_type

type class_attr =
  | CPA of cpaentry list
  | Class_Other of string * string

type code_attr =
  | Certificate of (Label.label * string) list
  | Code_Other of string * string

val parsers : (string * string, string * string, code_attr, class_attr) attribute_parsers
val compilers :  (string * string, string * string, code_attr, class_attr) Compile.attribute_compilers
val decompilers :  (string * string, string * string, code_attr, class_attr) Decompile.attribute_decompilers
val formatters :  (string * string, string * string, code_attr, class_attr) attribute_formatters

(** Definitions of class, method and field access flags *)

(**{1 Access Flags}

   This module contains the definitions of the allowed access flags
   for classes, methods and fields. *)

(** Class access flags. *)
type class_flags =
    { c_public     : bool
    ; c_private    : bool (** inner classes only *)
    ; c_protected  : bool (** inner classes only *)
    ; c_static     : bool (** inner classes only *)
    ; c_final      : bool
    ; c_super      : bool
    ; c_interface  : bool
    ; c_abstract   : bool
    ; c_synthetic  : bool
    ; c_annotation : bool
    ; c_enum       : bool
    }

(** A value of {!class_flags} with all flags set to [false] *)
val empty_class_flags : class_flags

(** Turn a list of flags into a 16 bit unsigned integer using the
    mapping specified in the JVM specification. *)
val ui16_of_class_flags : class_flags -> int

(** Convert a 16 bit unsigned integer into a list of flags using the
    mapping specified by the JVM specification. *)
val class_flags_of_ui16 : int -> class_flags


(** Field access flags. *)
type field_flags =
    { f_public     : bool
    ; f_private    : bool
    ; f_protected  : bool
    ; f_static     : bool
    ; f_final      : bool
    ; f_volatile   : bool
    ; f_transient  : bool
    ; f_synthetic  : bool
    ; f_enum       : bool
    }

(** A value of {!field_flags} with all flags set to [false] *)
val empty_field_flags : field_flags

(** Turn a list of flags into a 16 bit unsigned integer using the
    mapping specified in the JVM specification. *)
val ui16_of_field_flags : field_flags -> int

(** Convert a 16 bit unsigned integer into a list of flags using the
    mapping specified by the JVM specification. *)
val field_flags_of_ui16 : int -> field_flags

(** Method access flags *)
type method_flags =
    { m_public       : bool
    ; m_private      : bool
    ; m_protected    : bool
    ; m_static       : bool
    ; m_final        : bool
    ; m_synchronized : bool
    ; m_bridge       : bool
    ; m_varargs      : bool
    ; m_native       : bool
    ; m_abstract     : bool
    ; m_strictfp     : bool
    ; m_synthetic    : bool
    }

(** A value of {!method_flags} with all flags set to [false] *)
val empty_method_flags : method_flags

(** Turn a list of flags into a 16 bit unsigned integer using the
    mapping specified in the JVM specification. *)
val ui16_of_method_flags : method_flags -> int

(** Convert a 16 bit unsigned integer into a list of flags using the
    mapping specified by the JVM specification. *)
val method_flags_of_ui16 : int -> method_flags

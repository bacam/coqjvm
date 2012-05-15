Require Import AnnotationIface.

Require Import BasicMachineTypes.

(* A module type for annotations with some unspecified form of specification. *)

Module Type GENERIC_ANNOTATION
  (B : BASICS).

Declare Module A : ANNOTATION B.

Parameter method_specification : Type.
Parameter method_spec : A.method_annotation -> method_specification.

End GENERIC_ANNOTATION.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

Require Import BasicMachineTypes.
Require Import AnnotationIface.
Require Import ResourceAlgebra.

(* For execution purposes we only need the resource granting part
   of any annotations so that we can keep track of what the resource
   limit is. *)

Module EvalAnnotations (B:BASICS) <: ANNOTATION B.

Definition code_annotation := unit.
Record method_annotation' : Set := mk_method_annotation {
  grants : option (res_expr B.Classname.t)
}.
Definition method_annotation := method_annotation'.
Definition class_annotation := unit.

Definition trivial_method_annotation := mk_method_annotation None.

End EvalAnnotations.
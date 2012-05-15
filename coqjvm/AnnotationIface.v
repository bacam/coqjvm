Require Import BasicMachineTypes.
Require Import ResourceAlgebra.

Module Type ANNOTATION
  (ANN_B : BASICS).

Parameter code_annotation : Type.
Parameter method_annotation : Type.
Parameter grants : method_annotation ->  option (res_expr ANN_B.Classname.t).
Parameter class_annotation : Type.

Parameter trivial_method_annotation : method_annotation.

End ANNOTATION.
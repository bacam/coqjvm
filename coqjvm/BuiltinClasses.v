Require Import BasicMachineTypes.
Require Import ClasspoolIface.
Require Import List.

Require Import AnnotationIface.
Require Import ClassDatatypesIface.

Module BuiltinClasses
  (B   : BASICS)
  (ANN : ANNOTATION B)
  (C   : CLASSDATATYPES B ANN)
  (CP  : CLASSPOOL B ANN C).

Definition j_l_Object_methods :=
  (C.MethodList.update C.MethodList.empty
    (B.init, C.mkDescriptor None nil)
    (C.mkMethod
      B.init
      (C.mkDescriptor None nil)
      true false false false false false false false
      (Some (C.mkCode 0 (S 0) (C.op_return::nil) nil))
      ANN.trivial_method_annotation)).

Definition j_l_Object_fields :=
  C.FieldList.empty.

Definition j_l_Object_pool :=
  C.ConstantPool.empty.

Definition j_l_Object := CP.j_l_Object j_l_Object_methods j_l_Object_fields j_l_Object_pool.

Definition initial_classes :=
  CP.initial_cert_classpool j_l_Object_methods j_l_Object_fields j_l_Object_pool.

End BuiltinClasses.
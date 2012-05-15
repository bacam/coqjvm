Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import Twosig.

Require Import AnnotationIface.

Module Type VIRTUALMETHODLOOKUP
  (VM_B : BASICS)
  (ANN : ANNOTATION VM_B)
  (VM_C : CLASSDATATYPES VM_B ANN)
  (VM_CP : CLASSPOOL VM_B ANN VM_C)
  (VM_A  : ASSIGNABILITY VM_B ANN VM_C VM_CP).

Definition lookup_minimal : VM_CP.cert_classpool -> VM_B.Classname.t -> VM_B.Classname.t -> (VM_B.Methodname.t * VM_C.descriptor) -> Prop
 := fun classes nmA nmB mdesc =>
    forall nmB' cB',
     VM_A.assignable classes (VM_C.ty_obj nmA) (VM_C.ty_obj nmB') ->
     VM_A.assignable classes (VM_C.ty_obj nmB') (VM_C.ty_obj nmB) ->
     VM_CP.class_loaded classes nmB' cB' ->
     VM_C.class_interface cB' = false ->
     nmB' <> nmB ->
        VM_C.MethodList.lookup (VM_C.class_methods cB') mdesc = None
     \/ exists m, VM_C.MethodList.lookup (VM_C.class_methods cB') mdesc = Some m /\ VM_C.method_static m = true.

Parameter lookup_minimal_refl : forall classes nm md c,
  VM_CP.class_loaded classes nm c ->
  VM_C.class_interface c = false ->
  lookup_minimal classes nm nm md.

Parameter lookup_minimal_mid : forall classes nmA nmB nmB' md,
  VM_A.assignable classes (VM_C.ty_obj nmA) (VM_C.ty_obj nmB') ->
  VM_A.assignable classes (VM_C.ty_obj nmB') (VM_C.ty_obj nmB) ->
  lookup_minimal classes nmA nmB md ->
  lookup_minimal classes nmB' nmB md.

Parameter lookup_minimal_preserved : forall classes classes' nmA cA nmB cB mdesc,
  VM_CP.class_loaded classes nmA cA ->
  VM_C.class_interface cA = false ->
  VM_CP.class_loaded classes nmB cB ->
  VM_C.class_interface cB = false ->
  lookup_minimal classes nmA nmB mdesc ->
  VM_CP.preserve_old_classes classes classes' ->
  lookup_minimal classes' nmA nmB mdesc.


Parameter lookup_virtual_method : forall classes nm d,
  (exists c, VM_CP.class_loaded classes nm c /\ VM_C.class_interface c = false) ->
  option { c : VM_C.class, m : VM_C.method |
     VM_CP.class_loaded classes (VM_C.class_name c) c /\
     VM_C.MethodList.lookup (VM_C.class_methods c) d = Some m /\
     VM_C.class_interface c = false /\
     VM_C.method_static m = false /\
     VM_A.assignable classes (VM_C.ty_obj nm) (VM_C.ty_obj (VM_C.class_name c)) /\
     lookup_minimal classes nm (VM_C.class_name c) d}.

End VIRTUALMETHODLOOKUP.

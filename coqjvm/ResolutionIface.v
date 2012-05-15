Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.

Require Import AnnotationIface.

Module Type RESOLUTION
  (R_B : BASICS)
  (ANN : ANNOTATION R_B)
  (R_C : CLASSDATATYPES R_B ANN)
  (R_CP : CLASSPOOL R_B ANN R_C)
  (R_A : ASSIGNABILITY R_B ANN R_C R_CP).

Notation "{LOAD c , p ~~> c2 & x : R_A | Q }" := (R_CP.load_type R_A (fun (c2:R_CP.cert_classpool) (x:R_A) => Q) c p) (at level 0, x at level 99, c2 at level 99) : type_scope.

Parameter resolve_class : forall (caller target:R_B.Classname.t) classes preclasses,
  {LOAD classes, preclasses ~~> classes' & c : R_C.class |
    R_CP.class_loaded classes' target c }.

Parameter resolve_method : forall (caller target:R_B.Classname.t) (m:R_B.Methodname.t) (d:R_C.descriptor) classes preclasses,
 {LOAD classes,preclasses ~~> classes' & p : R_C.class * R_C.method |
    R_CP.class_loaded classes' (R_C.class_name (fst p)) (fst p) /\
    R_C.MethodList.lookup (R_C.class_methods (fst p)) (m,d) = Some (snd p) /\
    R_A.assignable classes' (R_C.ty_obj target) (R_C.ty_obj (R_C.class_name (fst p))) }.

Parameter resolve_interface_method : forall (caller target:R_B.Classname.t) (m:R_B.Methodname.t) (d:R_C.descriptor) classes preclasses,
 {LOAD classes,preclasses ~~> classes' & p : R_C.class * R_C.method |
    R_CP.class_loaded classes' (R_C.class_name (fst p)) (fst p) /\
    R_C.MethodList.lookup (R_C.class_methods (fst p)) (m,d) = Some (snd p) /\
    R_A.assignable classes' (R_C.ty_obj target) (R_C.ty_obj (R_C.class_name (fst p))) }.

Parameter resolve_field : forall (caller target:R_B.Classname.t) (f_nm:R_B.Fieldname.t) (j_ty:R_C.java_type) classes preclasses,
 {LOAD classes,preclasses ~~> classes' & p : R_C.class * R_C.field |
    R_CP.class_loaded classes' (R_C.class_name (fst p)) (fst p) /\
    R_C.FieldList.lookup (R_C.class_fields (fst p)) (f_nm,j_ty) = Some (snd p) }.

Hypothesis preserve_resolve_class : forall caller target classesA classesA' classesB preclasses (p:R_CP.preserve_old_classes classesA classesA') o c c_ex,
 resolve_class caller target classesA preclasses = R_CP.load_ok _ p o c c_ex ->
 R_CP.preserve_old_classes classesA classesB ->
 R_CP.only_add_from_preclasses classesA classesB preclasses ->
 exists classesB', exists pB : R_CP.preserve_old_classes classesB classesB', exists oB, exists c_exB,
   resolve_class caller target classesB preclasses = R_CP.load_ok _ pB oB c c_exB
   /\ R_CP.preserve_old_classes classesA' classesB'
   /\ R_CP.only_add_from_preclasses classesA' classesB' preclasses.

Hypothesis preserve_resolve_method : forall caller nm m d classesA classesA' classesB preclasses p o cm HA,
  resolve_method caller nm m d classesA preclasses = R_CP.load_ok _ (classes':=classesA') p o cm HA ->
  R_CP.preserve_old_classes classesA classesB ->
  R_CP.only_add_from_preclasses classesA classesB preclasses ->
  exists classesB', exists pB, exists oB, exists HB,
  resolve_method caller nm m d classesB preclasses = R_CP.load_ok _ (classes':=classesB') pB oB cm HB.

Hypothesis preserve_resolve_interface_method : forall caller nm m d classesA classesA' classesB preclasses p o cm HA,
  resolve_interface_method caller nm m d classesA preclasses = R_CP.load_ok _ (classes':=classesA') p o cm HA ->
  R_CP.preserve_old_classes classesA classesB ->
  R_CP.only_add_from_preclasses classesA classesB preclasses ->
  exists classesB', exists pB, exists oB, exists HB,
  resolve_interface_method caller nm m d classesB preclasses = R_CP.load_ok _ (classes':=classesB') pB oB cm HB.

Hypothesis preserve_resolve_field : forall caller nm f_nm f_ty classesA classesA' classesB preclasses p o cf HA,
  resolve_field caller nm f_nm f_ty classesA preclasses = R_CP.load_ok _ (classes':=classesA') p o cf HA ->
  R_CP.preserve_old_classes classesA classesB ->
  R_CP.only_add_from_preclasses classesA classesB preclasses ->
  exists classesB', exists pB, exists oB, exists HB,
  resolve_field caller nm f_nm f_ty classesB preclasses = R_CP.load_ok _ (classes':=classesB') pB oB cf HB.

End RESOLUTION.

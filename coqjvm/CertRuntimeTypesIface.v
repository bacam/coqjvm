Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import Twosig.
Require Import List.
Require Import StoreIface.
Require Import Heap.

Require Import AnnotationIface.

Module Type CERTRUNTIMETYPES
  (RDT_B  : BASICS)
  (ANN : ANNOTATION RDT_B)
  (RDT_C  : CLASSDATATYPES RDT_B ANN)
  (RDT_CP : CLASSPOOL RDT_B ANN RDT_C)
  (RDT_A  : ASSIGNABILITY RDT_B ANN RDT_C RDT_CP).

Inductive rt_val : Set :=
  | rt_int    : RDT_B.Int32.t -> rt_val
  | rt_addr   : option Heap.addr_t -> rt_val
  | rt_long   : rt_val
  | rt_double : rt_val
  | rt_float  : rt_val.

Definition val_category : rt_val -> RDT_C.value_category :=
  fun v => match v with
  | rt_int _  => RDT_C.category1
  | rt_addr _ => RDT_C.category1
  | rt_long   => RDT_C.category2
  | rt_double => RDT_C.category2
  | rt_float  => RDT_C.category1
  end.

Record frame : Type := mkFrame
 { frame_op_stack : list rt_val
 ; frame_lvars    : list (option rt_val) (* a local variable entry is None if it is the second part of a cat2 value, or has not been initialised yet *)
 ; frame_pc       : nat
 ; frame_code     : RDT_C.code
 ; frame_method   : RDT_C.method
 ; frame_class    : RDT_C.class
 }.

Parameter cert_heap : RDT_CP.cert_classpool -> Type.
Parameter cert_fieldstore : forall classes, cert_heap classes -> Type.

Parameter empty_heap : forall classes, cert_heap classes.
(* FIXME: say that no objects exist in the empty heap? *)
Parameter empty_fieldstore : forall classes heap, cert_fieldstore classes heap.

Record pre_state (A:Type) : Type := mkState
 { state_frame_stack   : list frame
 ; state_classes       : RDT_CP.cert_classpool
 ; state_object_heap   : cert_heap state_classes
 ; state_static_fields : cert_fieldstore state_classes state_object_heap
 ; state_res           : A
 ; state_reslimit      : A
 }.
Implicit Arguments mkState [A].

(* Facts about cert_heap *)
Parameter preserve_cert_heap : forall classesA classesB,
  cert_heap classesA ->
  RDT_CP.preserve_old_classes classesA classesB ->
  cert_heap classesB.
Implicit Arguments preserve_cert_heap [classesA classesB].

Parameter object_field_value : forall classes, cert_heap classes -> Heap.addr_t -> RDT_B.Classname.t -> RDT_B.Fieldname.t -> RDT_C.java_type -> rt_val -> Prop.
Parameter object_class       : forall classes, cert_heap classes -> Heap.addr_t -> RDT_B.Classname.t -> Prop.
Parameter object_exists      : forall classes, cert_heap classes -> Heap.addr_t -> Prop.

Definition heap_preserve_classes :=
  fun classes (heap heap':cert_heap classes) =>
  forall addr cls_nm, object_class classes heap addr cls_nm ->
                      object_class classes heap' addr cls_nm.

Definition heap_preserve_most_fields :=
  fun classes (heap heap':cert_heap classes) addr fld_cls fld_nm fld_ty =>
  forall addr' fld_cls' fld_nm' fld_ty' v,
    object_field_value classes heap addr' fld_cls' fld_nm' fld_ty' v ->
    (addr <> addr' \/ (fld_cls,fld_nm,fld_ty) <> (fld_cls',fld_nm',fld_ty')) ->
    object_field_value classes heap' addr' fld_cls' fld_nm' fld_ty' v.

Definition heap_preserve_fields :=
  fun classes (heap heap':cert_heap classes) =>
  forall addr fld_cls fld_nm fld_ty v,
    object_field_value classes heap addr fld_cls fld_nm fld_ty v ->
    object_field_value classes heap' addr fld_cls fld_nm fld_ty v.

Definition heap_preserve_existence :=
  fun classes (heap heap':cert_heap classes) =>
  forall addr,
    object_exists classes heap addr ->
    object_exists classes heap' addr.

(* FIXME: this is wrong: we should have different datatypes for stack and heap
   data *)
Inductive typed_val (classes:RDT_CP.cert_classpool) (heap:cert_heap classes)
                  : rt_val -> RDT_C.java_type -> Prop :=
| typed_int     : forall i, typed_val classes heap (rt_int i) RDT_C.ty_int
| typed_byte    : forall i, typed_val classes heap (rt_int i) RDT_C.ty_byte
| typed_short   : forall i, typed_val classes heap (rt_int i) RDT_C.ty_short
| typed_char    : forall i, typed_val classes heap (rt_int i) RDT_C.ty_char
| typed_boolean : forall i, typed_val classes heap (rt_int i) RDT_C.ty_boolean
| typed_float   : typed_val classes heap rt_float RDT_C.ty_float
| typed_long    : typed_val classes heap rt_long RDT_C.ty_long
| typed_double  : typed_val classes heap rt_double RDT_C.ty_double
| typed_null    : forall ref_ty, typed_val classes heap (rt_addr None) (RDT_C.ty_ref ref_ty)
| typed_addr    : forall a clsnm clsnm',
    object_class classes heap a clsnm ->
    RDT_A.assignable classes (RDT_C.ty_obj clsnm) (RDT_C.ty_obj clsnm') ->
    typed_val classes heap (rt_addr (Some a)) (RDT_C.ty_ref (RDT_C.ty_obj clsnm')).

Parameter type_check_rt_val : forall classes heap v ty, {typed_val classes heap v ty}+{~typed_val classes heap v ty}.

Hypothesis object_field_value_unique : forall classes heap addr fld_cls fld_nm fld_ty v v',
  object_field_value classes heap addr fld_cls fld_nm fld_ty v ->
  object_field_value classes heap addr fld_cls fld_nm fld_ty v' ->
  v = v'.

Hypothesis object_class_unique : forall classes heap addr cls_nm cls_nm',
  object_class classes heap addr cls_nm ->
  object_class classes heap addr cls_nm' ->
  cls_nm = cls_nm'.
Implicit Arguments object_class_unique [classes heap addr cls_nm cls_nm'].

Hypothesis field_value_implies_exists : forall classes heap addr fld_cls fld_nm fld_ty v,
  object_field_value classes heap addr fld_cls fld_nm fld_ty v ->
  object_exists classes heap addr.

Hypothesis object_class_implies_class_exists : forall classes heap addr cls_nm,
  object_class classes heap addr cls_nm ->
  exists c, RDT_CP.class_loaded classes cls_nm c /\ RDT_C.class_interface c = false.
Implicit Arguments object_class_implies_class_exists [classes heap addr cls_nm].

Hypothesis object_class_implies_exists : forall classes heap addr cls_nm,
  object_class classes heap addr cls_nm ->
  object_exists classes heap addr.

Hypothesis preserve_object_field_value : forall classesA classesB heap addr fld_cls fld_nm fld_ty v poc,
  object_field_value classesA heap addr fld_cls fld_nm fld_ty v ->
  object_field_value classesB (preserve_cert_heap heap poc) addr fld_cls fld_nm fld_ty v.

Hypothesis preserve_object_class : forall classesA classesB heap addr cls_nm poc,
  object_class classesA heap addr cls_nm ->
  object_class classesB (preserve_cert_heap heap poc) addr cls_nm.

Hypothesis preserve_object_exists : forall classesA classesB heap addr poc,
  object_exists classesA heap addr ->
  object_exists classesB (preserve_cert_heap heap poc) addr.

Parameter heap_lookup_field  : forall classes (heap:cert_heap classes) (addr:addr_t) (fld_cls:RDT_B.Classname.t) (fld_nm:RDT_B.Fieldname.t) (fld_ty:RDT_C.java_type),
  { v : rt_val | object_field_value classes heap addr fld_cls fld_nm fld_ty v }
 +{ ~object_exists classes heap addr }.
Implicit Arguments heap_lookup_field [classes].

Parameter heap_lookup_class  : forall classes (heap:cert_heap classes) (addr:addr_t),
  { cls_nm : RDT_B.Classname.t | object_class classes heap addr cls_nm }
 +{ ~object_exists classes heap addr }.
Implicit Arguments heap_lookup_class [classes].

Parameter heap_update_field  : forall classes (heap:cert_heap classes) (addr:addr_t) (fld_cls:RDT_B.Classname.t) (fld_nm:RDT_B.Fieldname.t) (fld_ty:RDT_C.java_type) (v:rt_val),
  typed_val classes heap v fld_ty ->
  { heap' : cert_heap classes | object_field_value classes heap' addr fld_cls fld_nm fld_ty v
                                /\ heap_preserve_classes classes heap heap'
                                /\ heap_preserve_most_fields classes heap heap' addr fld_cls fld_nm fld_ty }
  +{ ~object_exists classes heap addr }.
Implicit Arguments heap_update_field [classes].

Parameter heap_new : forall classes (heap:cert_heap classes) (cls_nm:RDT_B.Classname.t),
  (exists c, RDT_CP.class_loaded classes cls_nm c /\ RDT_C.class_interface c = false) ->
  { heap' : cert_heap classes, addr : addr_t |
     object_class classes heap' addr cls_nm
     /\ ~object_exists classes heap addr
     /\ heap_preserve_existence classes heap heap'
     /\ heap_preserve_classes classes heap heap'
     /\ heap_preserve_fields classes heap heap' }.
Implicit Arguments heap_new [classes].

Parameter fieldstore_value : forall (classes:RDT_CP.cert_classpool)
                                    (heap:cert_heap classes)
                                    (fields:cert_fieldstore classes heap)
                                    (fld_cls:RDT_B.Classname.t)
                                    (fld_nm:RDT_B.Fieldname.t)
                                    (fld_ty:RDT_C.java_type)
                                    (v:rt_val),
                                    Prop.

Parameter preserve_cert_fieldstore_over_classes : forall
   (classesA:RDT_CP.cert_classpool)
   (classesB:RDT_CP.cert_classpool)
   (heap:cert_heap classesA)
   (fields:cert_fieldstore classesA heap)
   (poc:RDT_CP.preserve_old_classes classesA classesB),
   cert_fieldstore classesB (preserve_cert_heap heap poc).
Implicit Arguments preserve_cert_fieldstore_over_classes [classesA classesB heap].

Hypothesis preserve_fieldstore_value_over_classes :
  forall classesA classesB heap fields fld_cls fld_nm fld_ty v
    (poc:RDT_CP.preserve_old_classes classesA classesB),
    fieldstore_value classesA heap fields fld_cls fld_nm fld_ty v ->
    fieldstore_value classesB (preserve_cert_heap heap poc) (preserve_cert_fieldstore_over_classes fields poc) fld_cls fld_nm fld_ty v.

Parameter preserve_cert_fieldstore_over_heap : forall
   (classes:RDT_CP.cert_classpool)
   (heapA:cert_heap classes)
   (heapB:cert_heap classes)
   (fields:cert_fieldstore classes heapA)
   (hpc:heap_preserve_classes classes heapA heapB),
   cert_fieldstore classes heapB.
Implicit Arguments preserve_cert_fieldstore_over_heap [classes heapA heapB].

Hypothesis preserve_fieldstore_value_over_heap :
  forall classes heapA heapB fields fld_cls fld_nm fld_ty v
    (hpc:heap_preserve_classes classes heapA heapB),
    fieldstore_value classes heapA fields fld_cls fld_nm fld_ty v ->
    fieldstore_value classes heapB (preserve_cert_fieldstore_over_heap fields hpc) fld_cls fld_nm fld_ty v.

Parameter fieldstore_lookup : forall
   (classes:RDT_CP.cert_classpool)
   (heap:cert_heap classes)
   (fields:cert_fieldstore classes heap)
   (fld_cls:RDT_B.Classname.t)
   (fld_nm:RDT_B.Fieldname.t)
   (fld_ty:RDT_C.java_type)
   (f_exists:exists c, exists f, RDT_CP.class_loaded classes fld_cls c
                                 /\ RDT_C.FieldList.lookup (RDT_C.class_fields c) (fld_nm,fld_ty) = Some f
                                 /\ RDT_C.field_static f = true),
   { v : rt_val | fieldstore_value classes heap fields fld_cls fld_nm fld_ty v }.
Implicit Arguments fieldstore_lookup [classes heap].

Definition fieldstore_preserve_most_fields :=
  fun classes heap fields fields' fld_cls fld_nm fld_ty =>
  forall fld_cls' fld_nm' fld_ty' v,
    fieldstore_value classes heap fields fld_cls' fld_nm' fld_ty' v ->
    (fld_cls,fld_nm,fld_ty) <> (fld_cls',fld_nm',fld_ty') ->
    fieldstore_value classes heap fields' fld_cls' fld_nm' fld_ty' v.

Parameter fieldstore_update : forall
   (classes:RDT_CP.cert_classpool)
   (heap:cert_heap classes)
   (fields:cert_fieldstore classes heap)
   (fld_cls:RDT_B.Classname.t)
   (fld_nm:RDT_B.Fieldname.t)
   (fld_ty:RDT_C.java_type)
   (v:rt_val)
   (well_typed:typed_val classes heap v fld_ty)
   (f_exists:exists c, exists f, RDT_CP.class_loaded classes fld_cls c
                                 /\ RDT_C.FieldList.lookup (RDT_C.class_fields c) (fld_nm,fld_ty) = Some f
                                 /\ RDT_C.field_static f = true),
   { fields' : cert_fieldstore classes heap |
       fieldstore_value classes heap fields' fld_cls fld_nm fld_ty v
    /\ fieldstore_preserve_most_fields classes heap fields fields' fld_cls fld_nm fld_ty }.
Implicit Arguments fieldstore_update [classes heap].

End CERTRUNTIMETYPES.
(** * Modelling of native methods. *)

Require Import ClassDatatypesIface.
Require Import CertRuntimeTypesIface.
Require Import JVMState.
Require Import Heap.
Require Import List.

Require Import BasicMachineTypes.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import ResolutionIface.
Require Import VirtualMethodLookupIface.
Require Import ResourceAlgebra.
Require Import AnnotationIface.

(** Given details of the method and state, the native methods implementation
    should provide the result of "executing" the method. *)

Module Type NATIVE_METHODS
  (B   : BASICS)
  (RA  : RESOURCE_ALGEBRA B)
  (ANN : ANNOTATION B)
  (C   : CLASSDATATYPES B ANN)
  (CP  : CLASSPOOL B ANN C)
  (A   : ASSIGNABILITY B ANN C CP)
  (R   : RESOLUTION B ANN C CP A)
  (VM  : VIRTUALMETHODLOOKUP B ANN C CP A)
  (RDT : CERTRUNTIMETYPES B ANN C CP A)
  (JVM : JVMSTATE B RA ANN C CP A R VM RDT).

Inductive resultval : Type :=
 | void : resultval
 | val  : RDT.rt_val -> resultval
 | exn  : Heap.addr_t   -> resultval.

Record result : Type :=
 { resval   : resultval
 ; classes  : CP.cert_classpool
 ; heap     : RDT.cert_heap classes
 ; static   : RDT.cert_fieldstore classes heap
 ; res      : RA.res
 ; reslimit : RA.res
 }.

Parameter native_invoke : C.class -> C.method -> list RDT.rt_val -> JVM.state -> option result.

End NATIVE_METHODS.

(** A dummy implementation where calling any native method causes the JVM to
    fail. *)

Module DummyNativeMethods
  (B   : BASICS)
  (RA  : RESOURCE_ALGEBRA B)
  (ANN : ANNOTATION B)
  (C   : CLASSDATATYPES B ANN)
  (CP  : CLASSPOOL B ANN C)
  (A   : ASSIGNABILITY B ANN C CP)
  (R   : RESOLUTION B ANN C CP A)
  (VM  : VIRTUALMETHODLOOKUP B ANN C CP A)
  (RDT : CERTRUNTIMETYPES B ANN C CP A)
  (JVM : JVMSTATE B RA ANN C CP A R VM RDT)
  <: NATIVE_METHODS B RA ANN C CP A R VM RDT JVM.

Inductive resultval : Type :=
 | void : resultval
 | val  : RDT.rt_val -> resultval
 | exn  : Heap.addr_t -> resultval.

Record result : Type :=
 { resval   : resultval
 ; classes  : CP.cert_classpool
 ; heap     : RDT.cert_heap classes
 ; static   : RDT.cert_fieldstore classes heap
 ; res      : RA.res
 ; reslimit : RA.res
 }.

Definition native_invoke : C.class -> C.method -> list RDT.rt_val -> JVM.state -> option result :=
  fun _ _ _ _ => None.

End DummyNativeMethods.
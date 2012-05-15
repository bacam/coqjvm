Require Import CertRuntimeTypesIface.
Require Import ResourceAlgebra.
Require Import Heap.

Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import ResolutionIface.
Require Import VirtualMethodLookupIface.
Require Import AnnotationIface.


Module Type JVMSTATE
  (B   : BASICS)
  (RA  : RESOURCE_ALGEBRA B)
  (ANN : ANNOTATION B)
  (C   : CLASSDATATYPES B ANN)
  (CP  : CLASSPOOL B ANN C)
  (A   : ASSIGNABILITY B ANN C CP)
  (R   : RESOLUTION B ANN C CP A)
  (VM  : VIRTUALMETHODLOOKUP B ANN C CP A)
  (RDT : CERTRUNTIMETYPES B ANN C CP A).

(* The JVM state *)

Definition state := RDT.pre_state RA.res.

(* Definition of the execution result type *)

Inductive exec_result : Type :=
| cont          : state -> exec_result
| stop          : state -> option RDT.rt_val -> exec_result
| stop_exn      : state -> Heap.addr_t -> exec_result
| wrong         : exec_result  (* JVM should not reach this state *)
| undefined     : exec_result. (* JVM behaviour not modelled *)

End JVMSTATE.

Module State
  (B   : BASICS)
  (RA  : RESOURCE_ALGEBRA B)
  (ANN : ANNOTATION B)
  (C   : CLASSDATATYPES B ANN)
  (CP  : CLASSPOOL B ANN C)
  (A   : ASSIGNABILITY B ANN C CP)
  (R   : RESOLUTION B ANN C CP A)
  (VM  : VIRTUALMETHODLOOKUP B ANN C CP A)
  (RDT : CERTRUNTIMETYPES B ANN C CP A)
  : JVMSTATE B RA ANN C CP A R VM RDT.

(* The JVM state *)

Definition state := RDT.pre_state RA.res.

(* Definition of the execution result type *)

Inductive exec_result : Type :=
| cont          : state -> exec_result
| stop          : state -> option RDT.rt_val -> exec_result
| stop_exn      : state -> Heap.addr_t -> exec_result
| wrong         : exec_result  (* JVM should not reach this state *)
| undefined     : exec_result. (* JVM behaviour not modelled *)

End State.

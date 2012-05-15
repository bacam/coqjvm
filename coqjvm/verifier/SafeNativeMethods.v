Require Import BasicMachineTypes.
Require Import ILL.ILLInterfaces.
Require Import Certificates.
Require Import VerifierAnnotationsIface.
Require Import ResourceAlgebra.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import ResolutionIface.
Require Import VirtualMethodLookupIface.
Require Import PreassignabilityIface.
Require Import CertRuntimeTypesIface.
Require Import JVMState.
Require Import NativeMethods.
Require Import AbstractLogic.
Require Import NativeMethodSpec.
Require Import ResourceLogicIface.

Require Import List.
Require Import ResourceLogic.

Module Type SAFE_NATIVE_METHODS
  (B    : BASICS)
  (BASESEM : ILL_BASE_SEMANTICS B)
  (SYN0 : ILL_SYNTAX B BASESEM.SYN)
  (CERT : CERTIFICATE         with Definition asn := BASESEM.SYN.formula)
  (AL   : ILL_TYPE B BASESEM.SYN SYN0)
  (ANN  : VERIFIER_ANNOTATIONS B AL CERT)
  (C    : CLASSDATATYPES B ANN.GA.A)
  (CP   : CLASSPOOL B ANN.GA.A C)
  (A    : ASSIGNABILITY B ANN.GA.A C  CP)
  (R    : RESOLUTION B ANN.GA.A C CP A)
  (RT   : CERTRUNTIMETYPES B ANN.GA.A C CP A)
  (RSEM : ILL_SEMANTICS B BASESEM SYN0)
  (VM   : VIRTUALMETHODLOOKUP B ANN.GA.A C CP A)
  (PA   : PREASSIGNABILITY B ANN.GA C CP A VM)
  (CLSNM: FSetInterface.S     with Definition E.t := B.Classname.t with Definition E.eq := B.Classname.eq)
  (NTSPC: NATIVE_METHOD_SPEC B ANN.GA.A)
  (RL   : RESOURCE_LOGIC B BASESEM SYN0 CERT AL ANN C CP A R RT RSEM VM PA CLSNM NTSPC)
  (JVM  : JVMSTATE B BASESEM.RA ANN.GA.A C CP A R VM RT).

Declare Module NM : NATIVE_METHODS B BASESEM.RA ANN.GA.A C CP A R VM RT JVM.

Import BASESEM.RA.

Parameter safe_native : forall preclasses privclasses s cls mth vls result P Q X r rem,
  RL.safe_state preclasses privclasses s ->
  CP.class_loaded (RT.state_classes _ s) (C.class_name cls) cls ->
  NTSPC.SpecTable.MapsTo (C.class_name cls, C.method_name mth) (C.method_annot mth) NTSPC.table ->
  ANN.method_spec (C.method_annot mth) = (P,Q,X) ->
  NM.native_invoke cls mth vls s = Some result ->
  (* given enough resources for the precondition... *)
  BASESEM.sat r P ->
  RT.state_res _ s :*: r :*: rem <: RT.state_reslimit _ s ->
  (* ... we can establish the postcondition, and ... *)
    exists r',
      match NM.resval result with NM.exn _ => BASESEM.sat r' X | _ => BASESEM.sat r' Q end /\
      (* ... any increase in resources is matched by an increase in the limit. *)
      NM.res result :*: r' :*: rem <: NM.reslimit result /\
      CP.preserve_old_classes (RT.state_classes _ s) (NM.classes result) /\
      CP.only_add_from_preclasses  (RT.state_classes _ s) (NM.classes result) preclasses
(* FIXME: currently we don't go through a state where the native method is on
   the stack, but we use the top of the stack to determine if we have permission
   to increase the resource limit; for now we forbid increasing the limit in
   native methods. *)
/\ RT.state_reslimit _ s = NM.reslimit result
.

End SAFE_NATIVE_METHODS.

Module SafeDummyNativeMethods
  (B    : BASICS)
  (BASESEM : ILL_BASE_SEMANTICS B)
  (SYN0 : ILL_SYNTAX B BASESEM.SYN)
  (CERT : CERTIFICATE         with Definition asn := BASESEM.SYN.formula)
  (AL   : ILL_TYPE B BASESEM.SYN SYN0)
  (ANN  : VERIFIER_ANNOTATIONS B AL CERT)
  (C    : CLASSDATATYPES B ANN.GA.A)
  (CP   : CLASSPOOL B ANN.GA.A C)
  (A    : ASSIGNABILITY B ANN.GA.A C  CP)
  (R    : RESOLUTION B ANN.GA.A C CP A)
  (RT   : CERTRUNTIMETYPES B ANN.GA.A C CP A)
  (RSEM : ILL_SEMANTICS B BASESEM SYN0)
  (VM   : VIRTUALMETHODLOOKUP B ANN.GA.A C CP A)
  (PA   : PREASSIGNABILITY B ANN.GA C CP A VM)
  (CLSNM: FSetInterface.S     with Definition E.t := B.Classname.t with Definition E.eq := B.Classname.eq)
  (NTSPC: NATIVE_METHOD_SPEC B ANN.GA.A)
  (RL   : RESOURCE_LOGIC B BASESEM SYN0 CERT AL ANN C CP A R RT RSEM VM PA CLSNM NTSPC)
  (JVM  : JVMSTATE B BASESEM.RA ANN.GA.A C CP A R VM RT)
  <: SAFE_NATIVE_METHODS B BASESEM SYN0 CERT AL ANN C CP A R RT RSEM VM PA CLSNM NTSPC RL JVM.

Module NM := DummyNativeMethods B BASESEM.RA ANN.GA.A C CP A R VM RT JVM.

Import BASESEM.RA.

Lemma safe_native : forall preclasses privclasses s cls mth vls result P Q X r rem,
  RL.safe_state preclasses privclasses s ->
  CP.class_loaded (RT.state_classes _ s) (C.class_name cls) cls ->
  NTSPC.SpecTable.MapsTo (C.class_name cls, C.method_name mth) (C.method_annot mth) NTSPC.table ->
  ANN.method_spec (C.method_annot mth) = (P,Q,X) ->
  NM.native_invoke cls mth vls s = Some result ->
  (* given enough resources for the precondition... *)
  BASESEM.sat r P ->
  RT.state_res _ s :*: r :*: rem <: RT.state_reslimit _ s ->
  (* ... we can establish the postcondition, and ... *)
    exists r',
      match NM.resval result with NM.exn _ => BASESEM.sat r' X | _ => BASESEM.sat r' Q end /\
      (* ... any increase in resources is matched by an increase in the limit. *)
      NM.res result :*: r' :*: rem <: NM.reslimit result /\
      CP.preserve_old_classes (RT.state_classes _ s) (NM.classes result) /\
      CP.only_add_from_preclasses  (RT.state_classes _ s) (NM.classes result) preclasses
/\ RT.state_reslimit _ s = NM.reslimit result
.
Proof.
  intros.
  unfold NM.native_invoke in H3.
  discriminate.
Qed.

End SafeDummyNativeMethods.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)


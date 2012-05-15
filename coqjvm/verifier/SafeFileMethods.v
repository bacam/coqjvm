Require Import ResourceLogicIface.
Require Import FileNativeMethods.
Require Import SafeNativeMethods.
Require Import NativeMethodSpec.
Require Import JVMState.
Require Import VerifierAnnotationsIface.
Require Import BasicMachineTypes.
Require Import ILL.ILLInterfaces.
Require Import Certificates.

Require Import List.
Require Import ListExt.
Require Import FMapFacts.

Require Import VerifierAnnotationsIface.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import ResolutionIface.
Require Import VirtualMethodLookupIface.
Require Import PreassignabilityIface.
Require Import CertRuntimeTypesIface.
Require Import AbstractLogic.

Module SafeFileMethods
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
  (FS  : FILENATIVESPEC B BASESEM.SYN SYN0 AL CERT ANN with Definition F.classnames := B.Classname.t with Definition F.nint := B.Int32.t)
  (RL   : RESOURCE_LOGIC B BASESEM SYN0 CERT AL ANN C CP A R RT RSEM VM PA CLSNM FS)
  (JVM  : JVMSTATE B BASESEM.RA ANN.GA.A C CP A R VM RT)
  <: SAFE_NATIVE_METHODS B BASESEM SYN0 CERT AL ANN C CP A R RT RSEM VM PA CLSNM FS RL JVM.

Module NM  := FileNativeMethods.FileNativeMethods B BASESEM.RA ANN.GA.A C CP A R VM RT JVM FS.F.

Module SF := FMapFacts.Facts FS.SpecTable.

Import BASESEM.RA.

Definition head_is {A:Type} (l:list A) (P:A->Prop) :=
  exists a, List.head l = Some a /\ P a.

Lemma safe_native : forall preclasses privclasses s cls mth vls result P Q X r rem,
  RL.safe_state preclasses privclasses s ->
  CP.class_loaded (RT.state_classes _ s) (C.class_name cls) cls ->
  FS.SpecTable.MapsTo (C.class_name cls, C.method_name mth) (C.method_annot mth) FS.table ->
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
  intros until rem. intros safe_state cls_loaded spec1 spec2 exec satP rem_limit.

  (* All of these methods are resource-neutral. *)
  exists r.

  unfold FS.table in spec1.
  unfold NM.native_invoke in exec.
  destruct (B.Classname.eq_dec (C.class_name cls) FS.F.fileclass) as [cls_eq|]; try discriminate.
   destruct (B.Methodname.eq_dec (C.method_name mth) FS.F.openmeth) as [mth_eq|]; [|
   destruct (B.Methodname.eq_dec (C.method_name mth) FS.F.readmeth) as [mth_eq|]; [|
   destruct (B.Methodname.eq_dec (C.method_name mth) FS.F.closemeth) as [mth_eq|]]];
    destruct vls; try discriminate;
    destruct r0;
    destruct vls; try discriminate;
    destruct s;
    injection exec as result_eq;
    subst;
    rewrite cls_eq, mth_eq in spec1;
    repeat (rewrite SF.add_mapsto_iff in spec1;
    destruct spec1 as [[[ceq meq] aeq]|[noteq spec1]]; try solve [destruct noteq;auto]; try clear noteq);
    try (rewrite <- aeq in spec2;
    injection spec2; intros; subst;
    simpl in *;
    unfold CP.only_add_from_preclasses;
    repeat split; auto using leq_refl, eq_refl, CP.preserve_old_classes_id).
Qed.

End SafeFileMethods.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

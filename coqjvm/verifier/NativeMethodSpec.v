Require Import AnnotationIface.
Require Import VerifierAnnotationsIface.
Require Import ILL.ILLInterfaces.
Require Import AbstractLogic.
Require Import FMapAVL.
Require Import OrderedTypeEx.

Require Import BasicMachineTypes.
Require Import Certificates.

Module Type NATIVE_METHOD_SPEC
  (B : BASICS)
  (A : ANNOTATION B).
  (* TO DO: perhaps we should also use the descriptor? *)

  Declare Module SpecTable : FMapInterface.S 
    with Definition E.t := (B.Classname.t * B.Methodname.t)%type
    with Definition E.eq := fun x y => (B.Classname.eq (fst x) (fst y) /\
                                        B.Methodname.eq (snd x) (snd y)).

  Parameter table : SpecTable.t A.method_annotation.

End NATIVE_METHOD_SPEC.

(* This really belongs with SafeNativeMethods, but extracting that is a pain. *)

Module DummyNativeSpec
  (B : BASICS)
  (A0 : ANNOTATION B) : NATIVE_METHOD_SPEC B A0.

Module A := A0.

Module Key := PairOrderedType B.Classname B.Methodname.
Module SpecTable := FMapAVL.Make Key.

Definition table := SpecTable.empty A.method_annotation.

End DummyNativeSpec.

(* This really belongs with SafeFileMethods. *)

Require Import FileNativeMethods.

Module Type FILENATIVESPEC
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B)
  (SYN : ILL_SYNTAX B BASESYN)
  (AL : ILL_TYPE B BASESYN SYN)
  (CERT : CERTIFICATE with Definition asn := AL.formula)
  (VA : VERIFIER_ANNOTATIONS B AL CERT).

Module A := VA.GA.A.
Declare Module F : FileImpl with Definition classnames := B.Classname.t with Definition methodnames := B.Methodname.t.

Declare Module SpecTable : FMapInterface.S 
  with Definition E.t := (B.Classname.t * B.Methodname.t)%type
  with Definition E.eq := fun x y => (B.Classname.eq (fst x) (fst y) /\
                                      B.Methodname.eq (snd x) (snd y)).

Definition table :=
  SpecTable.add (F.fileclass,F.openmeth)
  (VA.Build_method_annotation'
    (BASESYN.f_i,
     BASESYN.f_i,
     BASESYN.f_i) None)
  (SpecTable.add (F.fileclass,F.readmeth)
    (VA.Build_method_annotation'
      (BASESYN.f_i,
        BASESYN.f_i,
        BASESYN.f_i) None)
    (SpecTable.add (F.fileclass,F.closemeth)
      (VA.Build_method_annotation'
        (BASESYN.f_i,
          BASESYN.f_i,
          BASESYN.f_i) None)
      (SpecTable.empty A.method_annotation))).

End FILENATIVESPEC.

(* Ensure it's a subtype of the right thing: *)
Module FNSsubtype
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B)
  (SYN : ILL_SYNTAX B BASESYN)
  (AL : ILL_TYPE B BASESYN SYN)
  (CERT : CERTIFICATE with Definition asn := AL.formula)
  (VA : VERIFIER_ANNOTATIONS B AL CERT)
  (FS:FILENATIVESPEC B BASESYN SYN AL CERT VA) : NATIVE_METHOD_SPEC B VA.GA.A := FS.

Module FileNativeSpec
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B)
  (SYN : ILL_SYNTAX B BASESYN)
  (AL  : ILL_TYPE B BASESYN SYN)
  (CERT : CERTIFICATE with Definition asn := AL.formula)
  (VA  : VERIFIER_ANNOTATIONS B AL CERT)
  (F0  : FileImpl with Definition classnames := B.Classname.t with Definition methodnames := B.Methodname.t)
                      <: FILENATIVESPEC B BASESYN SYN AL CERT VA.

Module A := VA.GA.A.
Module F := F0.
Module Key := PairOrderedType B.Classname B.Methodname.
Module SpecTable := FMapAVL.Make Key.

Definition table :=
  SpecTable.add (F.fileclass,F.openmeth)
  (VA.Build_method_annotation'
    (BASESYN.f_i,
     BASESYN.f_i,
     BASESYN.f_i) None)
  (SpecTable.add (F.fileclass,F.readmeth)
    (VA.Build_method_annotation'
      (BASESYN.f_i,
        BASESYN.f_i,
        BASESYN.f_i) None)
    (SpecTable.add (F.fileclass,F.closemeth)
      (VA.Build_method_annotation'
        (BASESYN.f_i,
          BASESYN.f_i,
          BASESYN.f_i) None)
      (SpecTable.empty A.method_annotation))).

End FileNativeSpec.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)


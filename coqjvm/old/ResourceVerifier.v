Require Import GenericVerifierIface.
Require Import GenericVerifier.
Require Import ClassDatatypesIface.
Require Import ILLInterfaces.
Require Import BasicMachineTypes.
Require Import OptionMonad.
Require Import OptionExt.
Require Import ClasspoolIface.
Require Import CertRuntimeTypesIface.
Require Import List.
Require Import Execution.
Require Import ResInstructionVerifier.
Require Import Certificates.

Module ResourceVerifier
        (B : BASICS)
        (SYN : ILL_SYNTAX with Module SYN.B := B)
        (CERT : CERTIFICATE with Definition asn := SYN.SYN.formula)
        (ANN : ILLANNOTATIONS with Module B:= B with Module SYN := SYN with Module CERT := CERT)
        (RA : RESOURCE_ALGEBRA with Module B := B)
        (C : CLASSDATATYPES with Module B := B with Module A := ANN)
        (CP : CLASSPOOL with Module B := B with Module C := C)
        (RT : CERTRUNTIMETYPES with Module B := B with Module C := C with Module CP := CP)
        (RSEM : ILL_SEMANTICS with Module RA := RA with Module SYN := SYN).

Module E := Execution.Execution B RA C CP RT.

Module RIV := ResInstructionVerifier.ResInstructionVerifier B SYN CERT C.

Module RCV := MkCodeVerifier B SYN CERT ANN C RIV.

Import SYN.
Import CERT.
Import RCV.
Import RSEM.
Import RA.



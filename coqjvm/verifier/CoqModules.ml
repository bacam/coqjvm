open Coqextract

module Filter = struct
  let f0 = ref (fun _ -> true)
  let f c = (!f0) c
end

module ClassnameSet = FSetAVL.Make (BasicsImpl.Classname)
module ResILLBase = ResILLBase.ResBaseSemantics (BasicsImpl) (Filter)
module ILL        = ILLImplementation.MkILLSyntax (BasicsImpl) (ResILLBase.SYN)
module Simplifier = ILLSimplifier.ILLSimplifier (BasicsImpl) (ResILLBase.SYN) (ILL)
module ILLAL      = AbstractLogic.ILL (BasicsImpl) (ResILLBase.SYN) (ILL)
module Cert       = Certificates.MkILLCert (ILLAL)
module Ann        = VerifierAnnotations.MkVerifierAnnotations (BasicsImpl) (ILLAL) (Cert)
module PlainAnn   = Ann.GA.A
module C          = MkClassDatatypes.MkClassDatatypes (BasicsImpl) (Ann.GA.A)
module CP         = MkClasspool.MkClasspool (BasicsImpl) (PlainAnn) (C)
module A          = Assignability.MkAssignability (BasicsImpl) (PlainAnn) (C) (CP)
module R          = MkResolution.MkResolution (BasicsImpl) (PlainAnn) (C) (CP) (A)
module RT         = CertRuntimeTypes.MkCertRuntimeTypes (BasicsImpl) (PlainAnn) (C) (CP) (A)
module VM         = MkVirtualMethodLookup.MkVirtualMethodLookup (BasicsImpl) (PlainAnn) (C) (CP) (A)
module PA         = Preassignability.MkPreassignability (BasicsImpl) (Ann.GA) (C) (CP) (A) (VM)
module RSEM       = ILLImplementation.MkILLSemantics (BasicsImpl) (ResILLBase) (ILL)
(*module NatMethSp  = NativeMethodSpec.DummyNativeSpec (BasicsImpl) (Ann.GA.A)*)
module NatMethSp  = NativeMethodSpec.FileNativeSpec (BasicsImpl) (ResILLBase.SYN) (ILL) (ILLAL) (Cert) (Ann) (FileNativeImpl)
module VCs        = VCs.VerificationConditions (BasicsImpl) (ILLAL)
module ResChecker = ResourceChecker.ResourceChecker (BasicsImpl) (ResILLBase) (ILL) (Cert) (ILLAL) (Ann) (C) (CP) (A) (R) (RT) (RSEM) (VM) (PA) (ClassnameSet) (NatMethSp) (VCs)
module BIC = Coqextract.BuiltinClasses.BuiltinClasses (BasicsImpl) (PlainAnn) (C) (CP)

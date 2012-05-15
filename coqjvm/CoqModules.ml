open Coqextract

module Filter = struct
  let f _ = true
end

module ClassnameSet = FSetAVL.Make (BasicsImpl.Classname)
module RA  = ClassResourceAlgebra.ClassResourceAlgebra (BasicsImpl) (Filter)
module EA  = EvalAnnotations.EvalAnnotations (BasicsImpl)
module C   = MkClassDatatypes.MkClassDatatypes (BasicsImpl) (EA)
module CP  = MkClasspool.MkClasspool (BasicsImpl) (EA) (C)
module A   = Assignability.MkAssignability (BasicsImpl) (EA) (C) (CP)
module R   = MkResolution.MkResolution (BasicsImpl) (EA) (C) (CP) (A)
module RDT = CertRuntimeTypes.MkCertRuntimeTypes (BasicsImpl) (EA) (C) (CP) (A)
module VM  = MkVirtualMethodLookup.MkVirtualMethodLookup (BasicsImpl) (EA) (C) (CP) (A)
module JVM = JVMState.State (BasicsImpl) (RA) (EA) (C) (CP) (A) (R) (VM) (RDT)
(*module NM  = NativeMethods.DummyNativeMethods (BasicsImpl) (RA) (EA) (C) (CP) (A) (R) (VM) (RDT) (JVM)*)
module NM  = FileNativeMethods.FileNativeMethods (BasicsImpl) (RA) (EA) (C) (CP) (A) (R) (VM) (RDT) (JVM) (FileNativeImpl)
module BIC = Coqextract.BuiltinClasses.BuiltinClasses (BasicsImpl) (EA) (C) (CP)
module E   = Execution.Execution (BasicsImpl) (RA) (EA) (C) (CP) (A) (R) (VM) (RDT) (JVM) (NM) (ClassnameSet)

module PlainAnn   = EA

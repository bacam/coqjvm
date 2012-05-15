Require MkClassDatatypes.
Require MkClasspool.
Require CertRuntimeTypes.
Require Assignability.
Require Preassignability.
Require Certificates.
Require ILL.ILLImplementation.
Require ILL.ILLSimplifier.
Require VerifierAnnotations.
Require ResILLBase.
Require ResourceChecker.
Require ClassResourceAlgebra.
Require MkResolution.
Require MkVirtualMethodLookup.
Require BuiltinClasses.
Require NativeMethodSpec.
Require FSetAVL.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" ["true" "false" ].
Extract Inductive sumor => "option" ["Some" "None" ].
Extract Inductive option => "option" ["Some" "None" ].
Extract Inductive unit => "unit" ["()"].
Extract Inductive nat => "Common.Types.nat" ["Common.Types.O" "Common.Types.S"].
Extract Inductive List.list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Recursive Extraction Library ResILLBase.
Recursive Extraction Library ILLImplementation.
Recursive Extraction Library ILLSimplifier.
Recursive Extraction Library Certificates.
Recursive Extraction Library MkClassDatatypes.
Recursive Extraction Library MkClasspool.
Recursive Extraction Library Assignability.
Recursive Extraction Library MkResolution.
Recursive Extraction Library CertRuntimeTypes.
Recursive Extraction Library MkVirtualMethodLookup.
Recursive Extraction Library Preassignability.
Recursive Extraction Library VerifierAnnotations.
Recursive Extraction Library AbstractLogic.
Recursive Extraction Library VCs.
Recursive Extraction Library GenericVerifier.
Recursive Extraction Library ResourceChecker.
Recursive Extraction Library BuiltinClasses.
Recursive Extraction Library NativeMethodSpec.
Recursive Extraction Library FSetAVL.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

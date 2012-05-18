Require Execution.
Require MkClasspool.
Require MkClassDatatypes.
Require CertRuntimeTypes.
Require Assignability.
Require MkResolution.
Require MkVirtualMethodLookup.
Require ClassResourceAlgebra.
Require JVMState.
Require NativeMethods.
Require FileNativeMethods.
Require EvalAnnotations.
Require FSetAVL.
Require BuiltinClasses.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" ["true" "false" ].
Extract Inductive sumor => "option" ["Some" "None" ].
Extract Inductive option => "option" ["Some" "None" ].
Extract Inductive unit => "unit" ["()"].
Extract Inductive nat => "Common.Types.nat" ["Common.Types.O" "Common.Types.S"].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Unset Extraction AutoInline.
Recursive Extraction Library Execution.
Recursive Extraction Library MkClasspool.
Recursive Extraction Library MkClassDatatypes.
Recursive Extraction Library Assignability.
Recursive Extraction Library MkResolution.
Recursive Extraction Library MkVirtualMethodLookup.
Recursive Extraction Library CertRuntimeTypes.
Recursive Extraction Library ClassResourceAlgebra.
Recursive Extraction Library JVMState.
Recursive Extraction Library NativeMethods.
Recursive Extraction Library FileNativeMethods.
Recursive Extraction Library EvalAnnotations.
Recursive Extraction Library FSetAVL.
Recursive Extraction Library BuiltinClasses.
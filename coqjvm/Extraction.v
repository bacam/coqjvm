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
Separate Extraction Execution MkClasspool MkClassDatatypes Assignability MkResolution MkVirtualMethodLookup CertRuntimeTypes ClassResourceAlgebra JVMState NativeMethods FileNativeMethods EvalAnnotations FSetAVL BuiltinClasses.
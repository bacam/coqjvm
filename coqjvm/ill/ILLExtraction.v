Require ILLImplementation.
Require ResILLBase.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" ["true" "false" ].
Extract Inductive sumor => "option" ["Some" "None" ].
Extract Inductive option => "option" ["Some" "None" ].
Extract Inductive unit => "unit" ["()"].
Extract Inductive nat => "Common.Types.nat" ["Common.Types.O" "Common.Types.S"].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Recursive Extraction Library ILLImplementation.
Recursive Extraction Library ResILLBase.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "." "ILL")
   End:
   *)

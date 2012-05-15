(* Coq interface to ocaml strings.  Note that we don't provide any facilities to
   mutate strings without copying, and the ocaml code probably shouldn't
   change them behind coq's back.

   The major advantages of these strings over the standard library's module are
   that you can actually examine these in ocamldebug, and class and method names
   are constructed from ocaml strings. *)

Require String.

Axiom MLString : Set.
Extract Constant MLString => "string".

(*
Axiom mlstring_of_string : String.string -> MLString.
Extract Constant mlstring_of_string => "Common.MLStringsImpl.mlstring_of_string".
*)

Axiom mlstring_append : MLString -> MLString -> MLString.
Notation "s1 'mlapp' s2" := (mlstring_append s1 s2) (at level 60, right associativity).
Extract Constant mlstring_append => "(^)".

Axiom mlstring_of_nat : nat -> MLString.
Extract Constant mlstring_of_nat => "Common.MLStringsImpl.mlstring_of_nat".

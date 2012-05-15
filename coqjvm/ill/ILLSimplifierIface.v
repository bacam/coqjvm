Require Import ILLInterfaces.

Require Import BasicMachineTypes.

Module Type ILL_SIMPLIFIER
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B)
  (SYN : ILL_SYNTAX B BASESYN).

Parameter simplify : BASESYN.formula -> BASESYN.formula.
Hypothesis simplify_ok : forall f, SYN.implies f (simplify f) /\ SYN.implies (simplify f) f.

End ILL_SIMPLIFIER.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "." "ILL")
   End:
   *)

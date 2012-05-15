(** * An abstract view of the logic for use in the generic verification modules. *)

Require Import BasicMachineTypes.
Require Import ResourceAlgebra.
Require Import MLStrings.

Require Import OrderedTypeEx.

(** ** The module type itself. *)

Module Type ABSTRACT_LOGIC (B:BASICS).

  (** The type of formula, ordering of them, comparison and string conversion
      (for error reporting). *)
  Parameter formula : Set.
  Declare Module FormulaOrdered : UsualOrderedType with Definition t := formula.
  Parameter formula_eq_dec : forall (x y:formula), {x = y} + {x <> y}.
  Parameter string_of_formula : formula -> MLString.
  
  (** A trivial formula for use in trivial specifications of trivial methods. *)
  Parameter trivial : formula.
  
  (** Type of proof terms. *)
  Parameter prf_term : Set.
  
  (** Implication and basic properties. *)
  Parameter implies : formula -> formula -> Prop.
  Hypothesis implies_refl : forall f, implies f f.
  Hypothesis implies_trans : forall A B C, implies A B -> implies B C -> implies A C.
  
  (** Transform a formula to allow for the extra resources promised in a "grants"
      annotation. *)
  Parameter given_resexpr_have : res_expr B.Classname.t -> formula -> formula.
  
  (** Some form of formula simplification, and it's correctness. *)
  Parameter simplify : formula -> formula.
  Hypothesis simplify_ok : forall f, implies f (simplify f) /\ implies (simplify f) f.
  
End ABSTRACT_LOGIC.


(** ** A refinement of the module type and an implementation for the ILL. *)

Require Import ILL.ILLInterfaces.
Require Import ILL.ILLSimplifier.


Module Type ILL_TYPE
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B)
  (SYN : ILL_SYNTAX B BASESYN).

Include Type ABSTRACT_LOGIC B
  with Definition formula := BASESYN.formula
  with Module FormulaOrdered := BASESYN.FormulaOrdered
  with Definition trivial := BASESYN.f_i
  with Definition formula_eq_dec := BASESYN.formula_eq_dec

  with Definition prf_term := SYN.prf_term

  with Definition implies := SYN.implies
  with Definition implies_refl := SYN.implies_refl
  with Definition implies_trans := SYN.implies_trans
  with Definition given_resexpr_have := fun g Q => BASESYN.f_lolli (SYN.resexpr_to_formula g) Q
  with Definition string_of_formula := BASESYN.string_of_formula.

End ILL_TYPE.

Module ILL
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B)
  (SYN : ILL_SYNTAX B BASESYN) : ILL_TYPE B BASESYN SYN.

  Definition formula := BASESYN.formula.
  Module FormulaOrdered := BASESYN.FormulaOrdered.
  Definition trivial := BASESYN.f_i.
  Definition formula_eq_dec := BASESYN.formula_eq_dec.
  Definition string_of_formula := BASESYN.string_of_formula.
  
  Definition prf_term := SYN.prf_term.
  
  Definition implies := SYN.implies.
  Definition implies_refl := SYN.implies_refl.
  Definition implies_trans := SYN.implies_trans.
  Definition given_resexpr_have := fun g Q => BASESYN.f_lolli (SYN.resexpr_to_formula g) Q.
  
  Module SIMP := ILLSimplifier B BASESYN SYN.
  
  Definition simplify := SIMP.simplify.
  Definition simplify_ok := SIMP.simplify_ok.
  
End ILL.
Require Import VerifierAnnotationsIface.
Require Import AbstractLogic.
Require Import BasicMachineTypes.
Require Import Certificates.
Require Import StoreIface.
Require Import Store.
Require Import GenericAnnotationIface.
Require Import AnnotationIface.
Require Import ResourceAlgebra.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require FMapAVL.

Module MkVerifierAnnotations
  (VA_B    : BASICS)
  (VA_AL   : ABSTRACT_LOGIC VA_B)
  (VA_CERT : CERTIFICATE with Definition asn := VA_AL.formula)
  : VERIFIER_ANNOTATIONS VA_B VA_AL VA_CERT.

Inductive constantpool_additional : Set :=
| cpae_static_method : VA_AL.formula -> VA_AL.formula -> VA_AL.formula -> constantpool_additional
| cpae_static_field
| cpae_instantiable_class
| cpae_instance_field
| cpae_instance_method : VA_AL.formula -> VA_AL.formula -> VA_AL.formula -> constantpool_additional
| cpae_instance_special_method : VA_AL.formula -> VA_AL.formula -> VA_AL.formula -> constantpool_additional
| cpae_interface_method : VA_AL.formula -> VA_AL.formula -> VA_AL.formula -> constantpool_additional
| cpae_classref.

Module CPAEntry.
Definition t := constantpool_additional.
End CPAEntry.
Module ConstantPoolAdditional := MkStore VA_B.ConstantPoolRef CPAEntry.

Module PTKey := PairOrderedType VA_AL.FormulaOrdered VA_AL.FormulaOrdered.
Module PTEntry.
Definition t := VA_AL.prf_term.
End PTEntry.
Module ProofTable := MkStore PTKey PTEntry.

Definition method_specification' := (VA_AL.formula * VA_AL.formula * VA_AL.formula)%type.
Definition method_specification := method_specification'.
Record method_annotation' : Set := {
  method_spec : method_specification
; grants : option (res_expr VA_B.Classname.t)
}.

Definition code_annotation := VA_CERT.Cert.t.
Definition method_annotation := method_annotation'.
Definition class_annotation := (ProofTable.t * ConstantPoolAdditional.t)%type.

Definition method_annotation_eqdec : forall (a1 a2:method_annotation), {a1 = a2} + {a1 <> a2}.
intros.
  repeat decide equality; auto using VA_B.Classname.eq_dec, VA_AL.formula_eq_dec.
Defined.

Definition trivial_method_annotation := Build_method_annotation' 
  (VA_AL.trivial, VA_AL.trivial, VA_AL.trivial)
  None.

Module GA <: GENERIC_ANNOTATION VA_B.
  Module A <: ANNOTATION VA_B.
    Module ANN_B := VA_B.

    Definition code_annotation := VA_CERT.Cert.t.
    Definition method_annotation := method_annotation'.
    Definition grants := grants.
    Definition class_annotation := (ProofTable.t * ConstantPoolAdditional.t)%type.

    Definition trivial_method_annotation := trivial_method_annotation.
  End A.

  Definition method_specification := method_specification'.
  Definition method_spec := method_spec.
End GA.

End MkVerifierAnnotations.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

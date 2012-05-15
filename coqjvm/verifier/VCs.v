Require FMapAVL.
Require FMapInterface.
Require OrderedTypeEx.
Require Import List.

Require Import BasicMachineTypes.
Require Import AbstractLogic.

Module Type VERIFICATION_CONDITIONS
  (VC_B    : BASICS)
  (VC_AL   : ABSTRACT_LOGIC VC_B).

(* Represent the verification conditions as a finite map from VC to it's source *)

Definition vc := (VC_AL.formula * VC_AL.formula)%type.
Declare Module VerificationConditions : FMapInterface.S
  with Definition E.t := vc.
Inductive vc_source : Set :=
| vc_spec : VC_B.Classname.t -> VC_B.Methodname.t -> nat -> vc_source
| vc_override : VC_B.Classname.t -> VC_B.Methodname.t -> vc_source.
Definition vc_sources := list vc_source.
Definition vcset := VerificationConditions.t vc_sources.

Definition simplify_vc (vc1:vc) : vc :=
  match vc1 with (f,f') => (VC_AL.simplify f, VC_AL.simplify f') end.

Definition add_vc (vcs:vcset) (vc1:vc) (source:vc_source) :=
  let vc' := simplify_vc vc1 in
  VerificationConditions.add vc'
  (match VerificationConditions.find vc' vcs with
     | None => source::nil
     | Some sources => source::sources
   end) vcs.

Parameter vc_eq : forall f1 f1' f2 f2',
  VerificationConditions.E.eq (f1,f1') (f2,f2') ->
  f1 = f2 /\ f1' = f2'.

End VERIFICATION_CONDITIONS.

Module VerificationConditions 
  (VC_B    : BASICS)
  (VC_AL : ABSTRACT_LOGIC VC_B)
  : VERIFICATION_CONDITIONS VC_B VC_AL.

(* Represent the verification conditions as a finite map from VC to it's source *)
Definition vc := (VC_AL.formula * VC_AL.formula)%type.
Module PTKey := OrderedTypeEx.PairOrderedType VC_AL.FormulaOrdered VC_AL.FormulaOrdered.
Module VerificationConditions := FMapAVL.Make PTKey.
Inductive vc_source : Set :=
| vc_spec : VC_B.Classname.t -> VC_B.Methodname.t -> nat -> vc_source
| vc_override : VC_B.Classname.t -> VC_B.Methodname.t -> vc_source.
Definition vc_sources := list vc_source.
Definition vcset := VerificationConditions.t vc_sources.

Definition simplify_vc (vc1:vc) : vc :=
  match vc1 with (f,f') => (VC_AL.simplify f, VC_AL.simplify f') end.

Definition add_vc (vcs:vcset) (vc1:vc) (source:vc_source) :=
  let vc' := simplify_vc vc1 in
  VerificationConditions.add vc'
  (match VerificationConditions.find vc' vcs with
     | None => source::nil
     | Some sources => source::sources
   end) vcs.

Lemma vc_eq : forall f1 f1' f2 f2',
  VerificationConditions.E.eq (f1,f1') (f2,f2') ->
  f1 = f2 /\ f1' = f2'.
Proof.
  intros.
  destruct H.
  auto.
Qed.

End VerificationConditions.


(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

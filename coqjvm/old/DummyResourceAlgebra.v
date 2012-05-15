Require Import ILLInterfaces.
Require Import BasicMachineTypes.
Require Import ResourceAlgebra.

Module DummyResourceAlgebra <: RESOURCE_ALGEBRA.

Definition res := unit.

Definition eq := fun (r1 r2:res) => True.

Notation "e1 [=] e2" := (eq e1 e2) (at level 70, no associativity).

Lemma eq_refl : forall r, r [=] r.
unfold eq. trivial.
Save.

Lemma eq_symm : forall r1 r2, r1 [=] r2 -> r2 [=] r1.
unfold eq. trivial.
Save.

Lemma eq_trans : forall r1 r2 r3, r1 [=] r2 -> r2 [=] r3 -> r1 [=] r3.
unfold eq. trivial.
Save.

Definition leq : res -> res -> Prop := fun r1 r2 => True.
Notation "e1 <: e2" := (leq e1 e2) (at level 75, no associativity).

Definition leq_dec : forall r1 r2, {r1 <: r2}+{~(r1 <: r2)}.
intros. left. unfold leq. trivial.
Defined.

Lemma leq_refl     : forall r1 r2, r1 [=] r2 -> r1 <: r2.
unfold leq. trivial.
Save.

Lemma leq_antisymm : forall r1 r2, r1 <: r2 -> r2 <: r1 -> r1 [=] r2.
unfold leq. trivial.
Save.

Lemma leq_trans    : forall r1 r2 r3, r1 <: r2 -> r2 <: r3 -> r1 <: r3.
unfold leq. trivial.
Save.

Definition combine : res -> res -> res := fun r1 r2 => tt.
Notation "e1 :*: e2" := (combine e1 e2) (at level 40, left associativity).

Lemma combine_morphism : forall r1 r2 r1' r2',
  r1 [=] r1' ->
  r2 [=] r2' ->
  r1 :*: r2 [=] r1' :*: r2'.
unfold eq. trivial.
Save.

Definition e : res := tt.

Lemma e_bottom : forall r, e <: r.
unfold leq. trivial.
Save.

Lemma e_combine_r : forall r, e :*: r [=] r.
unfold eq. trivial.
Save.

Lemma r_combine_e : forall r, r :*: e [=] r.
unfold eq. trivial.
Save.

Lemma combine_assoc : forall r1 r2 r3, r1 :*: (r2 :*: r3) [=] (r1 :*: r2) :*: r3.
unfold eq. trivial.
Save.

Lemma combine_symm  : forall r1 r2, r1 :*: r2 [=] r2 :*: r1.
unfold eq. trivial.
Save.

Lemma combine_order : forall r1 r1' r2 r2',
                                       r1 <: r1' -> r2 <: r2' ->
                                       r1 :*: r2 <: r1' :*: r2'.
unfold leq. trivial.
Save.

Definition bang : res -> res := fun r => tt.
Notation "! e" := (bang e) (at level 35, right associativity).

Lemma bang_unit : forall r, r <: !r.
unfold leq. trivial.
Save.

Lemma bang_mult : forall r, !!r <: !r.
unfold leq. trivial.
Save.

Lemma bang_codup : forall r, !r :*: !r <: !r.
unfold leq. trivial.
Save.

Lemma bang_e : !e [=] e.
unfold eq. trivial.
Save.

Lemma bang_combine : forall r1 r2, !(r1 :*: r2) [=] !r1 :*: !r2.
unfold eq. trivial.
Save.

Lemma bang_order : forall r1 r2, r1 <: r2 -> !r1 <: !r2.
unfold leq. trivial.
Save.

Lemma bang_morphism : forall r1 r2, r1 [=] r2 -> !r1 [=] !r2.
unfold eq. trivial.
Save.

Definition atom := unit.
Definition res_of_atom : atom -> res := fun a => tt.
Definition atom_eq_dec : forall (a1 a2:atom), {a1=a2}+{a1<>a2}.
intros. destruct a1. destruct a2. left. reflexivity.
Save.

End DummyResourceAlgebra.

Module DummyResourceAlgebraConstants (B0:BASICS) <: RESOURCE_ALGEBRA_CONSTANTS.

Module RA := DummyResourceAlgebra.
Module B:=B0.

Definition r_new := fun (x:B.Classname.t) => tt.

End DummyResourceAlgebraConstants.

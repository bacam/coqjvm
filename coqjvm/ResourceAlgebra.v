Require Import BasicMachineTypes.
Require Import Setoid.
Require List.

(* Definition for expressing resources in annotations. An RA will
   have a function to convert this to a resource, a logic will have
   a function to convert this to a formula. *)
Definition res_expr (R:Set) : Set := List.list (bool * R).


Module Type RESOURCE_ALGEBRA
  (RA_B : BASICS).

Parameter res : Type.

Parameter eq : res -> res -> Prop.
Notation "e1 [=] e2" := (eq e1 e2) (at level 70, no associativity).

Axiom eq_refl : forall r, r [=] r.
Axiom eq_symm : forall r1 r2, r1 [=] r2 -> r2 [=] r1.
Axiom eq_trans : forall r1 r2 r3, r1 [=] r2 -> r2 [=] r3 -> r1 [=] r3.

Add Relation res eq
 reflexivity proved by eq_refl
 symmetry proved by eq_symm
 transitivity proved by eq_trans as ra_eq_rel.


Parameter leq : res -> res -> Prop.
Notation "e1 <: e2" := (leq e1 e2) (at level 75, no associativity).

Axiom leq_refl     : forall r1 r2, r1 [=] r2 -> r1 <: r2.
Axiom leq_antisymm : forall r1 r2, r1 <: r2 -> r2 <: r1 -> r1 [=] r2.
Axiom leq_trans    : forall r1 r2 r3, r1 <: r2 -> r2 <: r3 -> r1 <: r3.

Declare Instance ra_leq_rel : PreOrder leq.
Declare Instance leq_morphism : Morphisms.Proper (eq ==> eq ==> iff) leq.

Parameter combine : res -> res -> res.
Notation "e1 :*: e2" := (combine e1 e2) (at level 40, left associativity).

Parameter e : res.

Axiom e_bottom : forall r, e <: r.
Axiom e_combine_r : forall r, e :*: r [=] r.
Axiom r_combine_e : forall r, r :*: e [=] r.
Axiom combine_assoc : forall r1 r2 r3, r1 :*: (r2 :*: r3) [=] (r1 :*: r2) :*: r3.
Axiom combine_symm  : forall r1 r2, r1 :*: r2 [=] r2 :*: r1.

Declare Instance combine_morphism_Proper : Morphisms.Proper (eq ==> eq ==> eq) combine.
Declare Instance combine_order_Proper : Morphisms.Proper (leq ++> leq ++> leq) combine.
Axiom combine_order : forall x y, x <: y -> forall x0 y0, x0 <: y0 -> x :*: x0 <: y :*: y0.

Parameter bang : res -> res.
Notation "! e" := (bang e) (at level 35, right associativity).

Axiom bang_unit : forall r, r <: !r.
Axiom bang_mult : forall r, !!r <: !r.
Axiom bang_codup : forall r, !r :*: !r <: !r.
Axiom bang_e : !e [=] e.
Axiom bang_combine : forall r1 r2, !(r1 :*: r2) [=] !r1 :*: !r2.

Parameter r_new : RA_B.Classname.t -> option res.

Declare Instance bang_morphism_Proper : Morphisms.Proper (eq ==> eq) bang.
Declare Instance bang_order_Proper : Morphisms.Proper (leq ++> leq) bang.


Fixpoint res_parse (expr:res_expr RA_B.Classname.t) :=
  match expr with
    | List.nil => e
    | (List.cons (true,c) t) => match r_new c with None => res_parse t | Some r => (!r) :*: (res_parse t) end
    | (List.cons (false,c) t) => match r_new c with None => res_parse t | Some r => r :*: (res_parse t) end
  end.

End RESOURCE_ALGEBRA.

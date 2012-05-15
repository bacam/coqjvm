Require Import BasicMachineTypes.
Require Import ClasspoolIface.
Require Import ClassDatatypesIface.
Require Import List.

Require Import AnnotationIface.

Module Type ASSIGNABILITY
  (A_B : BASICS)
  (ANN : ANNOTATION A_B)
  (A_C : CLASSDATATYPES A_B ANN)
  (A_CP : CLASSPOOL A_B ANN A_C).

(* Assignability *)

Inductive sub_class (classes:A_CP.cert_classpool) : A_B.Classname.t -> A_B.Classname.t -> Prop :=
| sub_class_refl : forall nm cwitness,
   A_CP.class_loaded classes nm cwitness ->
   sub_class classes nm nm
| sub_class_step : forall nm nm_t s_nm c,
   A_CP.class_loaded classes nm c ->
   A_C.class_super_class c = Some s_nm ->
   sub_class classes s_nm nm_t ->
   sub_class classes nm nm_t.

Hypothesis sub_class_trans : forall classes a b c,
  sub_class classes a b ->
  sub_class classes b c ->
  sub_class classes a c.

Hypothesis preserve_subclass : forall classesA classesB A A_B,
  sub_class classesA A A_B ->
  A_CP.preserve_old_classes classesA classesB ->
  sub_class classesB A A_B.

Hypothesis preserve_subclass_rev : forall classesA classesB nm_s c_s nm_t,
  A_CP.class_loaded classesA nm_s c_s ->
  sub_class classesB nm_s nm_t ->
  A_CP.preserve_old_classes classesA classesB ->
  sub_class classesA nm_s nm_t.

Inductive direct_super_interface (classes:A_CP.cert_classpool) : list A_B.Classname.t -> A_B.Classname.t -> Prop :=
| d_inter_here : forall nmT interfaces,
   direct_super_interface classes (nmT::interfaces) nmT
| d_inter_step_up : forall interfaces nmX cX nmT,
   A_CP.class_loaded classes nmX cX ->
   A_C.class_interface cX = true ->
   direct_super_interface classes (A_C.class_interfaces cX) nmT ->
   direct_super_interface classes (nmX::interfaces) nmT
| d_inter_step_along : forall interfaces nmT nmX,
   direct_super_interface classes interfaces nmT ->
   direct_super_interface classes (nmX::interfaces) nmT.

Definition class_implements classes nmS nmT :=
 exists nmS', exists cS',
   A_CP.class_loaded classes nmS' cS' /\
   A_C.class_interface cS' = false /\
   sub_class classes nmS nmS' /\
   direct_super_interface classes (A_C.class_interfaces cS') nmT.

Hypothesis cl_impls_direct : forall classes nmS cS nmT,
  A_CP.class_loaded classes nmS cS ->
  A_C.class_interface cS = false ->
  direct_super_interface classes (A_C.class_interfaces cS) nmT ->
  class_implements classes nmS nmT.
Implicit Arguments cl_impls_direct [classes nmS cS nmT].

Hypothesis cl_impls_super: forall classes nmS cS nm_superS nmT,
  A_CP.class_loaded classes nmS cS ->
  A_C.class_super_class cS = Some nm_superS ->
  class_implements classes nm_superS nmT ->
  class_implements classes nmS nmT.
Implicit Arguments cl_impls_super [classes nmS cS nm_superS nmT].

Parameter assignable : A_CP.cert_classpool -> A_C.java_ref_type -> A_C.java_ref_type -> Prop.
Parameter is_assignable : forall classes S T, {assignable classes S T}+{~assignable classes S T}.

Hypothesis assignable_class_class : forall classes nmS nmT cS cT,
   A_CP.class_loaded classes nmS cS ->
   A_CP.class_loaded classes nmT cT ->
   A_C.class_interface cS = false ->
   A_C.class_interface cT = false ->
   sub_class classes nmS nmT ->
   assignable classes (A_C.ty_obj nmS) (A_C.ty_obj nmT).
Implicit Arguments assignable_class_class [classes nmS nmT cS cT].

Hypothesis assignable_class_interface : forall classes nmS nmT cS cT nmS' cS',
   A_CP.class_loaded  classes nmS cS ->
   A_CP.class_loaded  classes nmT cT ->
   A_CP.class_loaded  classes nmS' cS' ->
   A_C.class_interface cS = false ->
   A_C.class_interface cS' = false ->
   A_C.class_interface cT = true ->
   sub_class classes nmS nmS' ->
   direct_super_interface classes (A_C.class_interfaces cS') nmT ->
   assignable classes (A_C.ty_obj nmS) (A_C.ty_obj nmT).
Implicit Arguments assignable_class_interface [classes nmS nmT cS cT nmS' cS'].

Hypothesis assignable_class_interface2 : forall classes nmS nmT cS cT,
  A_CP.class_loaded classes nmS cS ->
  A_CP.class_loaded classes nmT cT ->
  A_C.class_interface cS = false ->
  A_C.class_interface cT = true ->
  class_implements classes nmS nmT ->
  assignable classes (A_C.ty_obj nmS) (A_C.ty_obj nmT).
Implicit Arguments assignable_class_interface2 [classes nmS nmT cS cT].

Hypothesis assignable_interface_class : forall classes nmS cS,
   A_CP.class_loaded  classes nmS cS ->
   A_C.class_interface cS = true ->
   assignable classes (A_C.ty_obj nmS) (A_C.ty_obj A_B.java_lang_Object).

Hypothesis assignable_interface_interface_refl : forall classes nmS cS,
   A_CP.class_loaded classes nmS cS ->
   A_C.class_interface cS = true ->
   assignable classes (A_C.ty_obj nmS) (A_C.ty_obj nmS).
Implicit Arguments assignable_interface_interface_refl [classes nmS cS].

Hypothesis assignable_interface_interface_strict : forall classes nmS nmT cS cT,
   A_CP.class_loaded  classes nmS cS ->
   A_CP.class_loaded  classes nmT cT ->
   A_C.class_interface cS = true ->
   A_C.class_interface cT = true ->
   direct_super_interface classes (A_C.class_interfaces cS) nmT ->
   assignable classes (A_C.ty_obj nmS) (A_C.ty_obj nmT).
Implicit Arguments assignable_interface_interface_strict [classes nmS nmT cS cT].

Hypothesis get_sub_class : forall classes A A_B cA cB,
  A_CP.class_loaded  classes A cA ->
  A_CP.class_loaded  classes A_B cB ->
  A_C.class_interface cA = false ->
  A_C.class_interface cB = false ->
  assignable classes (A_C.ty_obj A) (A_C.ty_obj A_B) ->
  sub_class classes A A_B.

Hypothesis get_class_implements : forall classes A A_B cA cB,
  A_CP.class_loaded  classes A cA ->
  A_CP.class_loaded  classes A_B cB ->
  A_C.class_interface cA = false ->
  A_C.class_interface cB = true ->
  assignable classes (A_C.ty_obj A) (A_C.ty_obj A_B) ->
  exists A', exists cA', A_CP.class_loaded  classes A' cA'
                         /\ A_C.class_interface cA' = false
                         /\ sub_class classes A A'
                         /\ direct_super_interface classes (A_C.class_interfaces cA') A_B.

Hypothesis preserve_assignable : forall classesA classesB nmS nmT,
  assignable classesA nmS nmT ->
  A_CP.preserve_old_classes classesA classesB ->
  assignable classesB nmS nmT.

Hypothesis preserve_assignable_rev : forall classesA classesB nmA cA nmB,
  assignable classesB (A_C.ty_obj nmA) (A_C.ty_obj nmB) ->
  A_CP.class_loaded classesA nmA cA ->
  A_C.class_interface cA = false ->
  A_CP.preserve_old_classes classesA classesB ->
  assignable classesA (A_C.ty_obj nmA) (A_C.ty_obj nmB).

Hypothesis assignable_refl : forall classes nmA cA,
  A_CP.class_loaded classes nmA cA ->
  assignable classes (A_C.ty_obj nmA) (A_C.ty_obj nmA).

Hypothesis assignable_trans : forall classes a b c,
  assignable classes a b ->
  assignable classes b c ->
  assignable classes a c.

Hypothesis assignable_shared_subclass : forall classes A A_B A_C cA cB cC,
  A_CP.class_loaded classes A cA ->
  A_CP.class_loaded classes A_B cB ->
  A_CP.class_loaded classes A_C cC ->
  A_C.class_interface cA = false ->
  A_C.class_interface cB = false ->
  A_C.class_interface cC = false ->
  assignable classes (A_C.ty_obj A) (A_C.ty_obj A_B) ->
  assignable classes (A_C.ty_obj A) (A_C.ty_obj A_C) ->
  assignable classes (A_C.ty_obj A_B) (A_C.ty_obj A_C) \/ assignable classes (A_C.ty_obj A_C) (A_C.ty_obj A_B).

Hypothesis assignable_shared_subclass_2 : forall classes A A_B A_C cA cB cC,
  A_CP.class_loaded classes A cA ->
  A_CP.class_loaded classes A_B cB ->
  A_CP.class_loaded classes A_C cC ->
  A_C.class_interface cA = false ->
  A_C.class_interface cB = false ->
  A_C.class_interface cC = true ->
  assignable classes (A_C.ty_obj A) (A_C.ty_obj A_B) ->
  assignable classes (A_C.ty_obj A) (A_C.ty_obj A_C) ->
     assignable classes (A_C.ty_obj A_B) (A_C.ty_obj A_C)
  \/ (exists B', exists cB', A_CP.class_loaded classes B' cB'
                             /\ A_C.class_interface cB' = false
                             /\ assignable classes (A_C.ty_obj B') (A_C.ty_obj A_B)
                             /\ assignable classes (A_C.ty_obj A) (A_C.ty_obj B')
                             /\ assignable classes (A_C.ty_obj B') (A_C.ty_obj A_C)).

Hypothesis subclass_distinct : forall classes nm c nm' nm_t,
  A_CP.class_loaded classes nm c ->
  A_C.class_super_class c = Some nm' ->
  A_C.class_interface c = false ->
  sub_class classes nm' nm_t ->
  nm <> nm_t.

Hypothesis superclass_loaded : forall classes nm_s c_s nm_t,
  A_CP.class_loaded classes nm_s c_s ->
  sub_class classes nm_s nm_t ->
  exists c, A_CP.class_loaded classes nm_t c.

Hypothesis assignable_loaded : forall classes nmA cA nmB,
  A_CP.class_loaded classes nmA cA ->
  assignable classes (A_C.ty_obj nmA) (A_C.ty_obj nmB) ->
  exists cB, A_CP.class_loaded classes nmB cB.

End ASSIGNABILITY.
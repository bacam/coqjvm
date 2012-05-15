Require Import BasicMachineTypes.
Require Import ClasspoolIface.
Require Import ClassDatatypesIface.
Require Import AssignabilityIface.
Require Import List.
Require Import VirtualMethodLookupIface.
Require Import GenericAnnotationIface.

Require Import AnnotationIface.

Module Type PREASSIGNABILITY
  (PA_B  : BASICS)
  (PA_GA : GENERIC_ANNOTATION PA_B)
  (PA_C  : CLASSDATATYPES PA_B PA_GA.A)
  (PA_CP : CLASSPOOL      PA_B PA_GA.A PA_C)
  (PA_A  : ASSIGNABILITY  PA_B PA_GA.A PA_C PA_CP)
  (PA_VM : VIRTUALMETHODLOOKUP PA_B PA_GA.A PA_C PA_CP PA_A).

Inductive pc_sub_class (classes:PA_CP.cert_classpool) (preclasses:PA_CP.Preclasspool.t) : PA_B.Classname.t -> PA_B.Classname.t -> Prop :=
| pc_sub_class_refl : forall c cl,
    PA_CP.Preclasspool.lookup preclasses c = Some cl ->
    (forall cl', ~ PA_CP.class_loaded classes c cl') ->
    pc_sub_class classes preclasses c c
| pc_sub_class_step : forall c c' c'' cl,
    PA_CP.Preclasspool.lookup preclasses c  = Some cl  ->
    (forall cl', ~ PA_CP.class_loaded classes c cl') ->
    cl.(PA_C.preclass_super_name) = Some c' ->
    pc_sub_class classes preclasses c' c'' ->
    pc_sub_class classes preclasses c c''.

Inductive pc_cross_sub_class (classes:PA_CP.cert_classpool) (preclasses:PA_CP.Preclasspool.t) : PA_B.Classname.t -> PA_B.Classname.t -> Prop :=
| pc_cross_sub_class_cross : forall c c' c'' cl,
    PA_CP.Preclasspool.lookup preclasses c  = Some cl  ->
    (forall cl', ~ PA_CP.class_loaded classes c cl') ->
    cl.(PA_C.preclass_super_name) = Some c' ->
    PA_A.sub_class classes c' c'' ->
    pc_cross_sub_class classes preclasses c c''
| pc_cross_sub_class_step : forall c c' c'' cl,
    PA_CP.Preclasspool.lookup preclasses c  = Some cl  ->
    (forall cl', ~ PA_CP.class_loaded classes c cl') ->
    cl.(PA_C.preclass_super_name) = Some c' ->
    pc_cross_sub_class classes preclasses c' c'' ->
    pc_cross_sub_class classes preclasses c c''.

Hypothesis pc_loaded_cross_super_class : forall classes classes' preclasses nm nmB,
  (forall c, ~PA_CP.class_loaded classes nmB c) ->
  pc_cross_sub_class classes' preclasses nm nmB ->
  PA_CP.preserve_old_classes classes classes' ->
  PA_CP.only_add_from_preclasses classes classes' preclasses ->
  pc_sub_class classes preclasses nm nmB.

Hypothesis pc_preserve_cross_sub_class : forall classes classes' preclasses nmA nmB c,
  PA_CP.class_loaded classes nmB c ->
  pc_cross_sub_class classes' preclasses nmA nmB ->
  PA_CP.preserve_old_classes classes classes' ->
  PA_CP.only_add_from_preclasses classes classes' preclasses ->
  pc_cross_sub_class classes preclasses nmA nmB.

Hypothesis pc_preserve_sub_class : forall classes classes' preclasses nmA nmB,
  pc_sub_class classes' preclasses nmA nmB ->
  (forall c, ~PA_CP.class_loaded classes' nmB c) ->
  PA_CP.preserve_old_classes classes classes' ->
  PA_CP.only_add_from_preclasses classes classes' preclasses ->
  pc_sub_class classes preclasses nmA nmB.

Hypothesis pc_loaded_sub_class : forall classes classes' preclasses nmA nmB,
  PA_A.sub_class classes' nmA nmB ->
  (forall c, ~PA_CP.class_loaded classes nmA c) ->
  (forall c, ~PA_CP.class_loaded classes nmB c) ->
  PA_CP.preserve_old_classes classes classes' ->
  PA_CP.only_add_from_preclasses classes classes' preclasses ->
  pc_sub_class classes preclasses nmA nmB.

Hypothesis pc_loaded_cross_sub_class : forall classes classes' preclasses nmA nmB cB,
  PA_A.sub_class classes' nmA nmB ->
  (forall c, ~PA_CP.class_loaded classes nmA c) ->
  PA_CP.class_loaded classes nmB cB ->
  PA_CP.preserve_old_classes classes classes' ->
  PA_CP.only_add_from_preclasses classes classes' preclasses ->
  pc_cross_sub_class classes preclasses nmA nmB.



Hypothesis cross_assignable_undo_step_2 : forall classes preclasses nm nmS pc nmS' c,
 pc_cross_sub_class classes preclasses nm nmS ->
 PA_CP.Preclasspool.lookup preclasses nm = Some pc ->
 PA_C.preclass_super_name pc = Some nmS' ->
 PA_CP.class_loaded classes nmS' c ->
 PA_A.assignable classes (PA_C.ty_obj nmS') (PA_C.ty_obj nmS).

Hypothesis pre_assignable_barrier : forall classes preclasses nmA nmS pcA nmS' cS' pcS,
 pc_sub_class classes preclasses nmA nmS ->
 PA_CP.Preclasspool.lookup preclasses nmA = Some pcA ->
 PA_CP.Preclasspool.lookup preclasses nmS = Some pcS ->
 PA_C.preclass_super_name pcA = Some nmS' ->
 PA_C.preclass_interface pcS = false ->
 PA_CP.class_loaded classes nmS' cS' ->
 nmA = nmS.

Hypothesis cross_assignable_undo_step : forall classes preclasses nm nmS nmS' pc,
 pc_cross_sub_class classes preclasses nm nmS ->
 PA_CP.Preclasspool.lookup preclasses nm = Some pc ->
 PA_C.preclass_super_name pc = Some nmS' ->
 (forall c, ~PA_CP.class_loaded classes nmS' c) ->
 pc_cross_sub_class classes preclasses nmS' nmS.

Hypothesis pre_assignable_undo_step : forall classes preclasses nm nmS nmS' pc pcS,
 pc_sub_class classes preclasses nm nmS ->
 PA_CP.Preclasspool.lookup preclasses nm = Some pc ->
 PA_CP.Preclasspool.lookup preclasses nmS = Some pcS ->
 PA_C.preclass_super_name pc = Some nmS' ->
 PA_C.preclass_interface pcS = false ->
 nm <> nmS ->
 pc_sub_class classes preclasses nmS' nmS.

Section WithClasses.

Variable classes:PA_CP.cert_classpool.
Variable preclasses:PA_CP.Preclasspool.t.

Inductive interface_reqs_method (iface : PA_B.Classname.t) : (PA_B.Methodname.t * PA_C.descriptor) -> PA_GA.method_specification -> Prop :=
| interface_reqs_method_cls : forall c mkey md,
    PA_CP.class_loaded classes iface c ->
    PA_C.MethodList.lookup (PA_C.class_methods c) mkey = Some md ->
    interface_reqs_method iface mkey (PA_GA.method_spec (PA_C.method_annot md))
| interface_reqs_method_precls : forall pc mth,
    (forall c, ~PA_CP.class_loaded classes iface c) ->
    PA_CP.Preclasspool.lookup preclasses iface = Some pc ->
    PA_C.has_premethod (PA_C.preclass_methods pc) (PA_C.premethod_name mth, PA_C.premethod_descriptor mth) mth ->
    interface_reqs_method iface (PA_C.premethod_name mth, PA_C.premethod_descriptor mth) (PA_GA.method_spec (PA_C.premethod_annot mth))
| interface_reqs_method_upcls : forall c iface' mth annot,
    PA_CP.class_loaded classes iface c ->
    In iface' (PA_C.class_interfaces c) ->
    interface_reqs_method iface' mth annot ->
    interface_reqs_method iface mth annot
| interface_reqs_method_upprecls : forall pc iface' mth annot,
    (forall c, ~PA_CP.class_loaded classes iface c) ->
    PA_CP.Preclasspool.lookup preclasses iface = Some pc ->
    In iface' (PA_C.preclass_super_interfaces pc) ->
    interface_reqs_method iface' mth annot ->
    interface_reqs_method iface mth annot.

Inductive minimal_methodspec (nm:PA_B.Classname.t) (md:PA_B.Methodname.t*PA_C.descriptor) (mspec:PA_GA.method_specification) : Prop :=
  | minimal_methodspec_pre : forall pc m,
    (forall c, ~PA_CP.class_loaded classes nm c) ->
    PA_CP.Preclasspool.lookup preclasses nm = Some pc ->
    PA_C.preclass_interface pc = false ->
    PA_C.has_premethod (PA_C.preclass_methods pc) md m ->
    PA_GA.method_spec (PA_C.premethod_annot m) = mspec ->
    PA_C.premethod_static m = false ->
    minimal_methodspec nm md mspec
  | minimal_methodspec_loaded : forall c nmS cS m,
    PA_CP.class_loaded classes nm c ->
    PA_C.class_interface c = false ->
    PA_A.sub_class classes nm nmS ->
    PA_VM.lookup_minimal classes nm nmS md ->
    PA_CP.class_loaded classes nmS cS ->
    PA_C.class_interface cS = false ->
    PA_C.MethodList.lookup (PA_C.class_methods cS) md = Some m ->
    PA_GA.method_spec (PA_C.method_annot m) = mspec ->
    PA_C.method_static m = false ->
    minimal_methodspec nm md mspec
  | minimal_methodspec_prestep : forall pc nmS,
    (forall c, ~PA_CP.class_loaded classes nm c) ->
    PA_CP.Preclasspool.lookup preclasses nm = Some pc ->
    (forall m', PA_C.has_premethod (PA_C.preclass_methods pc) md m' -> PA_C.premethod_static m' = true) ->
    PA_C.preclass_super_name pc = Some nmS ->
    PA_C.preclass_interface pc = false ->
    minimal_methodspec nmS md mspec ->
    minimal_methodspec nm md mspec.

Inductive should_implement : PA_B.Classname.t -> PA_B.Classname.t -> Prop :=
| should_implement_loaded : forall nmA nmB cA cB iface,
  PA_CP.class_loaded classes nmA cA ->
  PA_CP.class_loaded classes nmB cB ->
  PA_C.class_interface cB = false ->
  PA_A.sub_class classes nmA nmB ->
  In iface (PA_C.class_interfaces cB) ->
  should_implement nmA iface
| should_implement_cross : forall nmA nmB cB iface,
  PA_CP.class_loaded classes nmB cB ->
  PA_C.class_interface cB = false ->
  pc_cross_sub_class classes preclasses nmA nmB ->
  In iface (PA_C.class_interfaces cB) ->
  should_implement nmA iface
| should_implement_pre : forall nmA nmB pcB iface,
  (forall c, ~PA_CP.class_loaded classes nmB c) ->
  PA_CP.Preclasspool.lookup preclasses nmB = Some pcB ->
  PA_C.preclass_interface pcB = false ->
  pc_sub_class classes preclasses nmA nmB ->
  In iface (PA_C.preclass_super_interfaces pcB) ->
  should_implement nmA iface.

End WithClasses.

Hypothesis does_not_implement : forall classes preclasses nm pc nmS iface,
  PA_CP.Preclasspool.lookup preclasses nm = Some pc ->
  (forall c, ~PA_CP.class_loaded classes nm c) ->
  should_implement classes preclasses nm iface ->
  ~In iface (PA_C.preclass_super_interfaces pc) ->
  PA_C.preclass_super_name pc = Some nmS ->
  should_implement classes preclasses nmS iface.

Hypothesis interface_reqs_preserved : forall classes classes' preclasses iface md annot,
  PA_CP.preserve_old_classes classes classes' ->
  PA_CP.only_add_from_preclasses classes classes' preclasses ->
 (interface_reqs_method classes preclasses iface md annot <->
  interface_reqs_method classes' preclasses iface md annot).

Hypothesis minimal_methodspec_preserved : forall classes classes' preclasses nm md mspec,
  PA_CP.preserve_old_classes classes classes' ->
  PA_CP.only_add_from_preclasses classes classes' preclasses ->
  (minimal_methodspec classes preclasses nm md mspec <->
   minimal_methodspec classes' preclasses nm md mspec).

Hypothesis should_implement_preserved_rev : forall classes classes' preclasses nm iface,
  PA_CP.preserve_old_classes classes classes' ->
  PA_CP.only_add_from_preclasses classes classes' preclasses ->
  should_implement classes' preclasses nm iface ->
  should_implement classes preclasses nm iface.

(* Convert an assignability requirement for an interface method to a
   preassignability requirement. *)
Hypothesis convert_iface_req : forall classes preclasses nm iface c cI md m,
  PA_CP.class_loaded classes nm c ->
  PA_CP.class_loaded classes iface cI ->
  PA_C.class_interface c = false ->
  PA_C.class_interface cI = true ->
  PA_A.assignable classes (PA_C.ty_obj nm) (PA_C.ty_obj iface) ->
  PA_C.MethodList.lookup (PA_C.class_methods cI) md = Some m ->
  exists base_iface,
    should_implement classes preclasses nm base_iface /\
    interface_reqs_method classes preclasses base_iface md (PA_GA.method_spec (PA_C.method_annot m)).


End PREASSIGNABILITY.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

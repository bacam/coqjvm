Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import StoreIface.
Require Import Twosig.
Require Import List.

Require Import AnnotationIface.

Module Type CLASSPOOL
  (CP_B : BASICS)
  (ANN  : ANNOTATION CP_B)
  (CP_C : CLASSDATATYPES CP_B ANN).

(* Exceptions *)
(* FIXME: this needs moving to somewhere else *)

Inductive exn : Set :=
| errIllegalAccess | errNoClassDefFound | errClassCast | errClassFormat
| errClassCircularity | errNoSuchMethod | errNoSuchField | errAbstractMethod 
| errIncompatibleClassChange | errInstantiation | errNullPointer | errVerify : exn.

Definition builtin_exception_to_class_name : exn -> CP_B.Classname.t :=
  fun e => match e with
  | errIllegalAccess           => CP_B.java_lang_IllegalAccessError
  | errNoClassDefFound         => CP_B.java_lang_NoClassDefFoundError
  | errClassCircularity        => CP_B.java_lang_ClassCircularityError
  | errNoSuchMethod            => CP_B.java_lang_NoSuchMethodError
  | errNoSuchField             => CP_B.java_lang_NoSuchFieldError
  | errAbstractMethod          => CP_B.java_lang_AbstractMethodError
  | errIncompatibleClassChange => CP_B.java_lang_IncompatibleClassChangeError
  | errInstantiation           => CP_B.java_lang_InstantiationError
  | errNullPointer             => CP_B.java_lang_NullPointerException
  | errClassCast               => CP_B.java_lang_ClassCastException
  | errClassFormat             => CP_B.java_lang_ClassFormatError
  | errVerify                  => CP_B.java_lang_VerifyError
  end.

(** * Class pools *)

Declare Module Preclasspool : STORE with Definition key := CP_B.Classname.t
                                    with Definition object := CP_C.preclass
                                    with Definition Key.eq := (@eq CP_B.Classname.t).

Parameter cert_classpool : Type.

Parameter class_loaded : cert_classpool -> CP_B.Classname.t -> CP_C.class -> Prop.

(** ** Definition of the initial classpool. *)

Section initial.

(** Parts of java.lang.Object that we don't specify here. *)
Variable methods:CP_C.MethodList.t.
Variable fields:CP_C.FieldList.t.
Variable pool:CP_C.ConstantPool.t.

Definition j_l_Object : CP_C.class :=
  CP_C.mkClass
  CP_B.java_lang_Object
  None
  List.nil
  true false false false false
  methods
  fields
  pool.

Parameter initial_cert_classpool :
  CP_C.MethodList.t -> CP_C.FieldList.t -> CP_C.ConstantPool.t -> cert_classpool.

Parameter initial_has_jlo : forall nm c,
  class_loaded (initial_cert_classpool methods fields pool) nm c ->
  nm = CP_B.java_lang_Object /\ c = j_l_Object.

End initial.

(** ** Properties of classes and certified classpools. *)

Inductive super_class_chain (classes:cert_classpool) : option CP_B.Classname.t -> Prop :=
| class_chain_end  : super_class_chain classes None
| class_chain_step : forall nm c,
   class_loaded classes nm c ->
   CP_C.class_interface c = false ->
   (forall c',
     class_loaded classes nm c' ->
     super_class_chain classes (CP_C.class_super_class c')) ->
   super_class_chain classes (Some nm).

Polymorphic Axiom super_class_chain_induction
     : forall (classes : cert_classpool)
         (P : forall o : option CP_B.Classname.t,
              super_class_chain classes o -> Prop),
       P None (class_chain_end classes) ->
       (forall nm c
          (e : class_loaded classes nm c)
          (e0 : CP_C.class_interface c = false)
          (s : forall c',
               class_loaded classes nm c' ->
               super_class_chain classes (CP_C.class_super_class c')),
        (forall c' (e1 : class_loaded classes nm c'),
         P (CP_C.class_super_class c') (s c' e1)) ->
        P (Some nm) (class_chain_step classes nm c e e0 s)) ->
       forall (o : option CP_B.Classname.t) (s : super_class_chain classes o),
       P o s.

Axiom scc_None : forall classes (ssc:super_class_chain classes None), ssc = class_chain_end classes.

Axiom scc_Some : forall classes nm (ssc:super_class_chain classes (Some nm)),
  exists c, exists c_exists, exists c_class, exists s,
    ssc = class_chain_step classes nm c c_exists c_class s.

Axiom scc_gives_class : forall classes o_nm nm c,
  o_nm = Some nm ->
  super_class_chain classes o_nm ->
  class_loaded classes nm c ->
  CP_C.class_interface c = false.
Implicit Arguments scc_gives_class [classes o_nm nm c].

Definition super_class_chain_inv : forall classes nm c o_nm,
  class_loaded classes nm c ->
  o_nm = Some nm ->
  super_class_chain classes o_nm ->
  super_class_chain classes (CP_C.class_super_class c)
  :=
fun classes nm c o_nm
  (H : class_loaded classes nm c)
  (H0 : o_nm = Some nm) (H1 : super_class_chain classes o_nm) =>
match
  H1 in (super_class_chain _ o)
  return (o = Some nm -> super_class_chain classes (CP_C.class_super_class c))
with
| class_chain_end _ =>
    fun H2 : None = Some nm =>
    let H3 :=
      eq_ind None
        (fun ee =>
         match ee with
         | Some _ => False
         | None => True
         end) I (Some nm) H2 in
    False_ind (super_class_chain classes (CP_C.class_super_class c)) H3
| class_chain_step _ nm0 c0 _ _ H2 =>
    fun H3 : Some nm0 = Some nm =>
    let H4 :=
      f_equal
        (fun e =>
         match e with
         | Some k => k
         | None => nm0
         end) H3 in
    let H5 :=
      eq_ind_r (fun nm1 => class_loaded classes nm1 c) H H4 in
    H2 c H5
end H0.
Implicit Arguments super_class_chain_inv [classes nm c o_nm].

Axiom super_class_chain_not_not_there : forall classes nm o_nm,
  o_nm = Some nm ->
  super_class_chain classes o_nm ->
  ~(~(exists c, class_loaded classes nm c)).
Implicit Arguments super_class_chain_not_not_there [classes nm o_nm].

Axiom cert_classpool_gives_scc : forall classes nm c,
  class_loaded classes nm c ->
  CP_C.class_interface c = false ->
  super_class_chain classes (CP_C.class_super_class c).
Implicit Arguments cert_classpool_gives_scc [classes nm c].

(* Interface hierarchies *)
Inductive good_interface_list2 : cert_classpool -> list CP_B.Classname.t -> Prop :=
| gil2_nil : forall classes,
   good_interface_list2 classes nil
| gil2_cons : forall classes i_nm rest i,
   class_loaded classes i_nm i ->
   CP_C.class_interface i = true ->
   (forall c',
     class_loaded classes i_nm c' ->
     good_interface_list2 classes (CP_C.class_interfaces c')) ->
   good_interface_list2 classes rest ->
   good_interface_list2 classes (i_nm::rest).

Polymorphic Axiom good_interface_list2_induction :
  forall
    P : forall (c : cert_classpool) (l : list CP_B.Classname.t),
      good_interface_list2 c l -> Prop,
      (forall classes : cert_classpool, P classes nil (gil2_nil classes)) ->
      (forall classes i_nm rest i
        (c : class_loaded classes i_nm i) (e : CP_C.class_interface i = true)
        (g : forall c', class_loaded classes i_nm c' -> good_interface_list2 classes (CP_C.class_interfaces c')),
        (forall c' (c0 : class_loaded classes i_nm c'),
          P classes (CP_C.class_interfaces c') (g c' c0)) ->
        forall g0 : good_interface_list2 classes rest,
          P classes rest g0 ->
          P classes (i_nm :: rest) (gil2_cons classes i_nm rest i c e g g0)) ->
      forall (c : cert_classpool) (l : list CP_B.Classname.t)
        (g : good_interface_list2 c l), P c l g.
        
Definition good_interface_list2_inv_1 : forall classes l i_nm rest i,
  good_interface_list2 classes l ->
  l = i_nm::rest ->
  class_loaded classes i_nm i ->
  good_interface_list2 classes (CP_C.class_interfaces i) :=
 fun classes t0 i_nm rest i H H0 H1 =>
  match
   H in (good_interface_list2 c l)
     return
     (l = i_nm :: rest ->
       class_loaded c i_nm i ->
       good_interface_list2 c (CP_C.class_interfaces i))
    with
    | gil2_nil classes0 =>
      fun H2 _ =>
        let H4 := eq_ind nil (fun e => match e with nil => True | _ :: _ => False end) I (i_nm :: rest) H2
          in
          False_ind (good_interface_list2 classes0 (CP_C.class_interfaces i)) H4
    | gil2_cons classes0 i_nm0 rest0 i0 H2 _ H4 H5 =>
      fun H6 H7 =>
        H4 i
        (let H8 :=
          f_equal
          (fun e  =>
            match e with
              | nil => i_nm0
              | t1 :: _ => t1
            end) H6 in
          (let H9 :=
            f_equal
            (fun e : list CP_B.Classname.t =>
              match e with
                | nil => rest0
                | _ :: l => l
              end) H6 in
            fun H10 : i_nm0 = i_nm =>
              let H11 :=
                eq_ind_r
                (fun i_nm1 : CP_B.Classname.t =>
                  class_loaded classes0 i_nm1 i0 ->
                  (forall c',
                    class_loaded classes0 i_nm1 c' ->
                    good_interface_list2 classes0 (CP_C.class_interfaces c')) ->
                  i_nm1 :: rest0 = i_nm :: rest -> class_loaded classes0 i_nm1 i)
                (fun (_ : class_loaded classes0 i_nm i0)
                  (_ : forall c',
                    class_loaded classes0 i_nm c' ->
                    good_interface_list2 classes0 (CP_C.class_interfaces c'))
                  (H13 : i_nm :: rest0 = i_nm :: rest) =>
                  let H14 :=
                    eq_ind_r
                    (fun rest1 : list CP_B.Classname.t =>
                      good_interface_list2 classes0 rest1 ->
                      i_nm :: rest1 = i_nm :: rest ->
                      class_loaded classes0 i_nm i)
                    (fun (_ : good_interface_list2 classes0 rest)
                      (_ : i_nm :: rest = i_nm :: rest) => H7) H9 in
                    H14 H5 H13) H10 in
                H11 H2 H4 H6) H8)
  end H0 H1.
Implicit Arguments good_interface_list2_inv_1 [classes l i_nm rest i].

Definition good_interface_list2_inv_2 : forall classes l i_nm rest,
  good_interface_list2 classes l ->
  l = i_nm::rest ->
  good_interface_list2 classes rest :=
fun (classes : cert_classpool) (l : list CP_B.Classname.t)
  (i_nm : CP_B.Classname.t) (rest : list CP_B.Classname.t)
  (H : good_interface_list2 classes l) (H0 : l = i_nm :: rest) =>
match
  H in (good_interface_list2 c l0)
  return (l0 = i_nm :: rest -> good_interface_list2 c rest)
with
| gil2_nil classes0 =>
    fun H1 : nil = i_nm :: rest =>
    let H2 :=
      eq_ind nil
        (fun e : list CP_B.Classname.t =>
         match e with
         | nil => True
         | _ :: _ => False
         end) I (i_nm :: rest) H1 in
    False_ind (good_interface_list2 classes0 rest) H2
| gil2_cons classes0 i_nm0 rest0 _ _ _ _ H4 =>
    fun H5 : i_nm0 :: rest0 = i_nm :: rest =>
    let H6 :=
      let H6 :=
        f_equal
          (fun e : list CP_B.Classname.t =>
           match e with
           | nil => i_nm0
           | t0 :: _ => t0
           end) H5 in
      (let H7 :=
         f_equal
           (fun e : list CP_B.Classname.t =>
            match e with
            | nil => rest0
            | _ :: l0 => l0
            end) H5 in
       fun _ : i_nm0 = i_nm => H7) H6 in
    eq_ind rest0
      (fun rest1 : list CP_B.Classname.t => good_interface_list2 classes0 rest1)
      H4 rest H6
end H0.
Implicit Arguments good_interface_list2_inv_2 [classes l i_nm rest].

Axiom good_interface_list2_not_not_there : forall classes l i_nm rest,
  good_interface_list2 classes l ->
  l = i_nm::rest ->
  ~(~(exists c, class_loaded classes i_nm c)).
Implicit Arguments good_interface_list2_not_not_there [classes l i_nm rest].

Axiom gil2_gives_interface : forall classes l i_nm rest i,
  good_interface_list2 classes l ->
  l = i_nm::rest ->
  class_loaded classes i_nm i ->
  CP_C.class_interface i = true.
Implicit Arguments gil2_gives_interface [classes l i_nm rest i].

Axiom gil2_inv_nil : forall classes (gil:good_interface_list2 classes nil),
  gil = gil2_nil classes.
Implicit Arguments gil2_inv_nil [classes].

Axiom gil2_inv_cons : forall classes i_nm rest (gil:good_interface_list2 classes (i_nm::rest)),
  exists i, exists i_exists, exists i_interface, exists go_up, exists go_along,
   gil = gil2_cons classes i_nm rest i i_exists i_interface go_up go_along.
Implicit Arguments gil2_inv_cons [classes i_nm rest].

Axiom cert_classpool_gives_gil2 : forall classes nm c,
  class_loaded classes nm c ->
  good_interface_list2 classes (CP_C.class_interfaces c).
Implicit Arguments cert_classpool_gives_gil2 [classes nm c].

(* FIXME: this is a quick hack *)
Parameter gather_class_exists_evidence : forall classes nm,
  unit+{exists c, class_loaded classes nm c /\ CP_C.class_interface c = false}.

Parameter class_loaded_dec : forall classes nm,
  {c : CP_C.class | class_loaded classes nm c}+{~(exists c, class_loaded classes nm c)}.

Parameter class_super_loaded : forall classes nm1 nm2 c1,
  class_loaded classes nm1 c1 ->
  CP_C.class_super_class c1 = Some nm2 ->
  exists c2, class_loaded classes nm2 c2.

Parameter class_super_interface : forall classes nm1 nm2 c1 c2,
  class_loaded classes nm1 c1 ->
  class_loaded classes nm2 c2 ->
  CP_C.class_super_class c1 = Some nm2 ->
  CP_C.class_interface c2 = false.

Parameter class_super_distinct : forall classes nm1 nm2 c1,
  class_loaded classes nm1 c1 ->
  CP_C.class_super_class c1 = Some nm2 ->
  CP_C.class_interface c1 = false ->
  nm1 <> nm2.

Parameter cert_classpool_names : forall classes nm c,
  class_loaded classes nm c ->
  class_loaded classes (CP_C.class_name c) c.
Implicit Arguments cert_classpool_names [classes nm c].

Axiom cert_classpool_names_2 : forall classes nm c,
  class_loaded classes nm c ->
  CP_C.class_name c = nm.
Implicit Arguments cert_classpool_names_2 [classes nm c].

Axiom class_loaded_unique : forall classes nm c1 c2,
  class_loaded classes nm c1 ->
  class_loaded classes nm c2 ->
  c1 = c2.
Implicit Arguments class_loaded_unique.

Axiom no_super_is_jlObject : forall classes nm c,
  class_loaded classes nm c ->
  CP_C.class_super_class c = None ->
  nm = CP_B.java_lang_Object.

Axiom cert_classpool_has_Object : forall classes,
  exists c,
   class_loaded classes CP_B.java_lang_Object c /\
   CP_C.class_super_class c = None /\
   CP_C.class_interfaces c = nil /\
   CP_C.class_interface c = false.

Axiom cert_classpool_gives_interface_super_class_Object : forall classes nm c,
  class_loaded classes nm c ->
  CP_C.class_interface c = true ->
  CP_C.class_super_class c = Some CP_B.java_lang_Object.
Implicit Arguments cert_classpool_gives_interface_super_class_Object [classes nm c].


(* Conversion from preclass to class *)

Definition precode_to_code (pre_code : CP_C.precode) : CP_C.code :=
 CP_C.mkCode (CP_C.precode_max_stack pre_code)
          (CP_C.precode_max_lvars pre_code)
          (CP_C.precode_code pre_code)
          (CP_C.precode_exception_table pre_code).

Definition premethod_to_method (pre_m : CP_C.premethod) : CP_C.method :=
 CP_C.mkMethod (CP_C.premethod_name pre_m)
            (CP_C.premethod_descriptor pre_m)
            (CP_C.premethod_public pre_m)
            (CP_C.premethod_protected pre_m)
            (CP_C.premethod_private pre_m)
            (CP_C.premethod_abstract pre_m)
            (CP_C.premethod_static pre_m)
            (CP_C.premethod_final pre_m)
            (CP_C.premethod_synchronized pre_m)
            (CP_C.premethod_strict pre_m)
            (match CP_C.premethod_code pre_m with None => None | Some pc => Some (precode_to_code pc) end)
            (CP_C.premethod_annot pre_m).

Parameter preclass_to_class : CP_C.preclass -> option CP_C.class.

Axiom preclass_to_class_props : forall pc c,
 preclass_to_class pc = Some c ->
   CP_C.class_name c = CP_C.preclass_name pc
 /\CP_C.class_constantpool c = CP_C.preclass_constantpool pc
 /\(forall md m, (exists pm, m = premethod_to_method pm /\ CP_C.has_premethod (CP_C.preclass_methods pc) md pm) <-> CP_C.MethodList.lookup (CP_C.class_methods c) md = Some m)
 /\CP_C.class_interface c = CP_C.preclass_interface pc
 /\CP_C.class_super_class c = CP_C.preclass_super_name pc
 /\CP_C.class_interfaces c = CP_C.preclass_super_interfaces pc.

(* Preservation properties *)
Definition preserve_old_classes :=
  fun classes classes' =>
  forall nm c, class_loaded classes nm c ->
               class_loaded classes' nm c.

Axiom preserve_old_classes_id : forall classes,
  preserve_old_classes classes classes.

Axiom preserve_old_classes_trans : forall classesA classesB classesC,
  preserve_old_classes classesA classesB ->
  preserve_old_classes classesB classesC ->
  preserve_old_classes classesA classesC.

Definition only_add_from_preclasses := fun classes classes' preclasses =>
  forall nm c, class_loaded classes' nm c ->
               ((exists pc, preclass_to_class pc = Some c /\ Preclasspool.lookup preclasses nm = Some pc /\ forall c', ~class_loaded classes nm c')
                \/ class_loaded classes nm c).

Axiom compose_only_add : forall classes classes' classes'' preclasses,
  preserve_old_classes classes classes' ->
  only_add_from_preclasses classes classes' preclasses ->
  only_add_from_preclasses classes' classes'' preclasses ->
  only_add_from_preclasses classes classes'' preclasses.

(* Class resolution and loading *)
Inductive load_type (A:Type) (P:cert_classpool -> A -> Prop) (classes:cert_classpool) (preclasses:Preclasspool.t) : Type :=
| load_ok : forall classes', preserve_old_classes classes classes' -> only_add_from_preclasses classes classes' preclasses -> forall a, P classes' a -> load_type A P classes preclasses
| load_err : forall classes', preserve_old_classes classes classes' -> only_add_from_preclasses classes classes' preclasses -> exn -> load_type A P classes preclasses.

Arguments Scope load_type [type_scope type_scope].

Notation "{LOAD c , p ~~> c2 & x : A | Q }" := (load_type A (fun (c2:cert_classpool) (x:A) => Q) c p) (at level 0, x at level 99, c2 at level 99) : type_scope.

Implicit Arguments load_ok [A classes preclasses classes'].
Implicit Arguments load_err [A classes preclasses classes'].

Axiom loader_dec : forall (A:Type) (P:cert_classpool -> A -> Prop) preclasses classes (f:{LOAD classes,preclasses ~~> classes' & x : A | P classes' x}),
    (exists classes', exists preserved : preserve_old_classes classes classes', exists only_add, exists a, exists H, f = load_ok _ preserved only_add a H)
 \/ (exists classes', exists preserved : preserve_old_classes classes classes', exists only_add, exists e, f = load_err _ preserved only_add e).
Implicit Arguments loader_dec [A P preclasses classes].

Parameter load_and_resolve_aux : forall target preclasses (PI:Preclasspool.wf_removals preclasses) classes,
  {LOAD classes, preclasses ~~> classes' & c : CP_C.class | class_loaded classes' target c }.

(* Preservation of resolution *)
Definition preclass_incl := fun preclasses preclasses' =>
  forall nm p, Preclasspool.lookup preclasses nm = Some p -> Preclasspool.lookup preclasses' nm = Some p.

Axiom preserve_load_and_resolve_aux :
  forall preclasses P preclasses' target classes classes' classes1 (preserved1:preserve_old_classes classes classes1) only_add1 c c_exists1,
  load_and_resolve_aux target preclasses P classes = load_ok _ preserved1 only_add1 c c_exists1 ->
  preserve_old_classes classes classes' ->
  only_add_from_preclasses classes classes' preclasses' ->
  preclass_incl preclasses preclasses' ->
  exists classes2, exists preserved2 : preserve_old_classes classes' classes2, exists only_add2, exists c_exists2,
    load_and_resolve_aux target preclasses P classes' = load_ok _ preserved2 only_add2 c c_exists2
    /\ preserve_old_classes classes1 classes2 /\ only_add_from_preclasses classes1 classes2 preclasses'.


End CLASSPOOL.












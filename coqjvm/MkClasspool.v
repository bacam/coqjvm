Require Import Setoid.
Require Import Store.
Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import List.
Require Import ListExt.
Require Import BoolExt.
Require Import OptionExt.
Require Import Eqdep_dec.
Require Import Twosig.

Require Import AnnotationIface.

Module MkClasspool (B : BASICS) (ANN : ANNOTATION B) (C : CLASSDATATYPES B ANN)
                 : CLASSPOOL B ANN C.

(* Firstly, the definition of class pools *)

Module Preclass.
Definition t := C.preclass.
End Preclass.
Module Preclasspool := Store.MkStore B.Classname Preclass.

Module Class.
Definition t:= C.class.
End Class.
Module Classpool := Store.MkStore B.Classname Class.

(* Set up some setoid stuffs : FIXME: should move this to a module *)

Add Relation B.Classname.t B.Classname.eq
 reflexivity proved by B.Classname.eq_refl
 symmetry proved by B.Classname.eq_sym
 transitivity proved by B.Classname.eq_trans
 as classname_setoid.

Add Morphism Classpool.lookup
 with signature (eq (A:=Classpool.t)) ==> B.Classname.eq ==> (eq (A:=option C.class))
 as classpool_lookup_mor.
apply Classpool.lookup_eq.
Save.

(* We now refine classpools to classpools with the invariants we require *)

Inductive good_interface_list : Classpool.t -> list B.Classname.t -> Prop :=
| gil_nil : forall classes,
   good_interface_list classes nil
| gil_cons : forall classes i_nm rest i,
   Classpool.lookup classes i_nm = Some i ->
   C.class_interface i = true ->
   good_interface_list classes (C.class_interfaces i) ->
   good_interface_list classes rest ->
   good_interface_list classes (i_nm::rest).

Inductive good_super_class (classes:Classpool.t) : option B.Classname.t -> Prop :=
| gsc_top  : good_super_class classes None
| gsc_step : forall super_c super_name,
   Classpool.lookup classes super_name = Some super_c -> (* FIXME: access permissions, finality etc. *)
   C.class_interface super_c = false ->
   good_super_class classes (C.class_super_class super_c) ->
   good_super_class classes (Some super_name).

Inductive class_invariant_aux : Classpool.t -> C.class -> Prop :=
| mk_class_invariant_class : forall classes c,
    C.class_interface c = false ->
    good_interface_list classes (C.class_interfaces c) ->
    good_super_class classes (C.class_super_class c) ->
    class_invariant_aux classes c
| mk_class_invariant_interface : forall classes c,
    C.class_interface c = true ->
    good_interface_list classes (C.class_interfaces c) ->
    C.class_super_class c = Some B.java_lang_Object ->
    class_invariant_aux classes c.

Inductive class_invariant : Classpool.t -> B.Classname.t -> C.class -> Prop :=
  mk_class_invariant : forall classes nm c,
    C.class_name c = nm ->
    (C.class_super_class c = None -> nm = B.java_lang_Object) ->
    class_invariant_aux classes c ->
    class_invariant classes nm c.

Record cert_classpool_aux : Type := mk_classpool
  { classpool           : Classpool.t
  ; classpool_invariant : forall nm c, Classpool.lookup classpool nm = Some c -> class_invariant classpool nm c
  ; classpool_Object    : exists c, Classpool.lookup classpool B.java_lang_Object = Some c
                                    /\ C.class_super_class c = None
                                    /\ C.class_interfaces c = nil
                                    /\ C.class_interface c = false
  }.
Definition cert_classpool := cert_classpool_aux.

Definition class_loaded := fun classes cls_nm cls => Classpool.lookup (classpool classes) cls_nm = Some cls.

(* Some simple facts that certified classpools give us *)
Lemma class_loaded_unique : forall classes nm c1 c2,
  class_loaded classes nm c1 ->
  class_loaded classes nm c2 ->
  c1 = c2.
intros classes nm c1 c2 c1_loaded c2_loaded.
unfold class_loaded in *. rewrite c1_loaded in c2_loaded. inversion c2_loaded. reflexivity.
Save.
    
Lemma cert_classpool_names : forall classes nm c,
  class_loaded classes nm c -> class_loaded classes (C.class_name c) c.
intros. destruct classes. unfold class_loaded in *. 
simpl in * |- *. generalize H. elim (classpool_invariant0 _ _ H).
intros. subst. assumption.
Save.
Implicit Arguments cert_classpool_names [classes nm c].

Lemma cert_classpool_names_2 : forall classes nm c,
  class_loaded classes nm c -> C.class_name c = nm.
intros. destruct classes. unfold class_loaded in *.
simpl in *. elim (classpool_invariant0 _ _ H). trivial.
Save.
Implicit Arguments cert_classpool_names_2 [classes nm c].

Lemma cert_classpool_gives_interface_super_class_Object : forall classes nm c,
  Classpool.lookup (classpool classes) nm = Some c ->
  C.class_interface c = true ->
  C.class_super_class c = Some B.java_lang_Object.
intros. destruct classes. 
pose (B:=classpool_invariant0 _ _ H). generalize B. destruct 1. 
destruct H3. 
 rewrite H3 in H0. discriminate.
 assumption.
Save.
Implicit Arguments cert_classpool_gives_interface_super_class_Object [classes nm c].

Lemma cert_classpool_has_Object : forall classes,
  exists c,
   Classpool.lookup (classpool classes) B.java_lang_Object = Some c /\
   C.class_super_class c = None /\
   C.class_interfaces c = nil /\
   C.class_interface c = false.
intros. destruct classes. assumption.
Save.

Lemma class_super_loaded : forall classes nm1 nm2 c1,
  class_loaded classes nm1 c1 ->
  C.class_super_class c1 = Some nm2 ->
  exists c2, class_loaded classes nm2 c2.
Proof.
  intros classes nm1 nm2 c1 c1_loaded c1_super.
  destruct classes as [pool invariant obj].
  unfold class_loaded in *.
  simpl in *.
  set (invariant1 := invariant _ _ c1_loaded).
  clearbody invariant1.
  destruct invariant1 as [pool nm1 cl1 name1 superobj invaux].
  destruct invaux as [pool cl1 notint intlist supers|pool cl1 isint intlist superobj'].
    rewrite c1_super in supers.
    inversion supers as [|cl2 nm2' lookup2].
    subst nm2'.
    exists cl2.
    assumption.

    rewrite c1_super in superobj'.
    injection superobj' as nm2isobj.
    subst nm2.
    destruct obj as [cl2 [cl2ex _]].
    exists cl2.
    assumption.
Qed.

Lemma class_super_interface : forall classes nm1 nm2 c1 c2,
  class_loaded classes nm1 c1 ->
  class_loaded classes nm2 c2 ->
  C.class_super_class c1 = Some nm2 ->
  C.class_interface c2 = false.
Proof.
  intros classes nm1 nm2 c1 c2 c1_loaded c2_loaded c1_super.
  destruct classes as [pool invariant obj].
  unfold class_loaded in *.
  simpl in *.
  set (invariant1 := invariant _ _ c1_loaded).
  clearbody invariant1.
  destruct invariant1 as [pool nm1 cl1 name1 superobj invaux].
  destruct invaux as [pool cl1 notint intlist supers|pool cl1 isint intlist superobj'].
    rewrite c1_super in supers.
    inversion supers as [|cl2 nm2' lookup2].
    subst nm2'.
    rewrite c2_loaded in lookup2.
    injection lookup2 as leq.
    subst cl2.
    assumption.

    rewrite c1_super in superobj'.
    injection superobj' as nm2isobj.
    destruct obj as [cl2 [cl2ex [_ [_ objnotint]]]].
    subst nm2.
    rewrite c2_loaded in cl2ex.
    injection cl2ex as cl2eq.
    subst cl2.
    assumption.
Qed.

Lemma class_super_distinct : forall classes nm1 nm2 c1,
  class_loaded classes nm1 c1 ->
  C.class_super_class c1 = Some nm2 ->
  C.class_interface c1 = false ->
  nm1 <> nm2.
Proof.
  intros until c1. intros loaded super notint nmeq.
  destruct classes as [pool invariant obj].
  unfold class_loaded in *.
  simpl in *.
  set (invariant1 := invariant _ _ loaded).
  clearbody invariant1.
  destruct invariant1 as [pool nm1 cl1 name1 superobj invaux].
  subst nm2.
  destruct invaux.
    set (x:=C.class_super_class c).
    assert (xeq: C.class_super_class c = x) by reflexivity.
    rewrite xeq in H1.
    induction H1.
      rewrite xeq in super.
      discriminate.

      rewrite xeq in super.
      injection super as super'.
      subst super_name.
      rewrite loaded in H1.
      injection H1 as H1'.
      subst super_c.
      apply IHgood_super_class.
      reflexivity.

    rewrite notint in H.
    discriminate.
Qed.

Lemma no_super_is_jlObject : forall classes nm c,
  class_loaded classes nm c ->
  C.class_super_class c = None ->
  nm = B.java_lang_Object.
intros. destruct classes.
pose (classpool_invariant0 _ _ H). generalize c0. clear c0. destruct 1. auto.
Save.

Definition class_loaded_dec : forall classes nm,
  {c : C.class | class_loaded classes nm c}+{~(exists c, class_loaded classes nm c)}.
unfold class_loaded.
intros. destruct (Classpool.lookup_informative (classpool classes) nm) as [[c c_exists] | no_c].
 left. exists c. assumption.
 right. unfold not. intro. destruct H as [c c_exists]. congruence.
Save.

Section initial.

Variable methods:C.MethodList.t.
Variable fields:C.FieldList.t.
Variable pool:C.ConstantPool.t.

Definition j_l_Object : C.class :=
  C.mkClass
  B.java_lang_Object
  None
  List.nil
  true false false false false
  methods
  fields
  pool.

Definition initial_classpool := Classpool.update Classpool.empty B.java_lang_Object j_l_Object.

Definition initial_cert_classpool : cert_classpool.
apply (mk_classpool initial_classpool).
 intros. unfold initial_classpool in *. assert (nm = B.java_lang_Object /\ j_l_Object = c).
  destruct (B.Classname.eq_dec nm B.java_lang_Object). rewrite e in H. rewrite Classpool.lookup_update in H. injection H as H'. tauto.
  rewrite Classpool.indep_lookup in H; auto. rewrite Classpool.lookup_empty in H. discriminate.
 destruct H0. subst nm c. apply mk_class_invariant; auto.
 apply mk_class_invariant_class; auto using gil_nil, gsc_top.

 exists j_l_Object; repeat split; auto.
 unfold initial_classpool. auto using Classpool.lookup_update.
Defined.

Lemma initial_has_jlo : forall nm c,
  class_loaded initial_cert_classpool nm c ->
  nm = B.java_lang_Object /\ c = j_l_Object.
Proof.
  unfold class_loaded. simpl.
  unfold initial_classpool. 
  intros.
  destruct (B.Classname.eq_dec nm B.java_lang_Object). subst nm. rewrite Classpool.lookup_update in H. injection H as H'. subst c. tauto.
  rewrite Classpool.indep_lookup in H; auto. rewrite Classpool.lookup_empty in H. discriminate.
Qed.

End initial.

(* Exceptions *)
(* FIXME: this needs moving to somewhere else *)

Inductive exn : Set :=
| errIllegalAccess | errNoClassDefFound | errClassCast | errClassFormat
| errClassCircularity | errNoSuchMethod | errNoSuchField | errAbstractMethod 
| errIncompatibleClassChange | errInstantiation | errNullPointer | errVerify : exn.

Definition builtin_exception_to_class_name : exn -> B.Classname.t :=
  fun e => match e with
  | errIllegalAccess           => B.java_lang_IllegalAccessError
  | errNoClassDefFound         => B.java_lang_NoClassDefFoundError
  | errClassCircularity        => B.java_lang_ClassCircularityError
  | errNoSuchMethod            => B.java_lang_NoSuchMethodError
  | errNoSuchField             => B.java_lang_NoSuchFieldError
  | errAbstractMethod          => B.java_lang_AbstractMethodError
  | errIncompatibleClassChange => B.java_lang_IncompatibleClassChangeError
  | errInstantiation           => B.java_lang_InstantiationError
  | errNullPointer             => B.java_lang_NullPointerException
  | errClassCast               => B.java_lang_ClassCastException
  | errClassFormat             => B.java_lang_ClassFormatError
  | errVerify                  => B.java_lang_VerifyError
  end.

(* Adding classes to the classpool *)

Lemma addition_preserves_good_interface_list :
  forall classes new_nm new_c l,
  Classpool.lookup classes new_nm = None ->
  good_interface_list classes l ->
  good_interface_list (Classpool.update classes new_nm new_c) l.
intros. 
induction H0.
 apply gil_nil.
 eapply gil_cons.
  destruct (B.Classname.eq_dec new_nm i_nm). 
   subst. rewrite H0 in H. discriminate.
   rewrite Classpool.indep_lookup. apply H0. apply n.
  assumption.
  auto.
  auto.
Save.

Lemma addition_preserves_good_super_class :
  forall classes new_nm new_c s_nm,
  Classpool.lookup classes new_nm = None ->
  good_super_class classes s_nm ->
  good_super_class (Classpool.update classes new_nm new_c) s_nm.
intros.
induction H0.
 apply gsc_top.
 eapply gsc_step.
  destruct (B.Classname.eq_dec new_nm super_name).
   subst. rewrite H0 in H. discriminate.
   rewrite Classpool.indep_lookup. apply H0. apply n.
  assumption.
  auto.
Save.

Lemma addition_preserves_invariant : forall classes new_nm nm c new_c,
  Classpool.lookup classes new_nm = None ->
  class_invariant classes nm c -> class_invariant (Classpool.update classes new_nm new_c) nm c.
intros. destruct H0. apply mk_class_invariant. 
 assumption.
 assumption.
 destruct H2. 
  apply mk_class_invariant_class.
   assumption. 
   apply addition_preserves_good_interface_list; assumption.
   apply addition_preserves_good_super_class; assumption.
  apply mk_class_invariant_interface.
   assumption.
   apply addition_preserves_good_interface_list; assumption.
   assumption.
Save.
Implicit Arguments addition_preserves_invariant [classes new_nm nm c new_c].

Definition precode_to_code (pre_code : C.precode) : C.code :=
 C.mkCode (C.precode_max_stack pre_code)
          (C.precode_max_lvars pre_code)
          (C.precode_code pre_code)
          (C.precode_exception_table pre_code).

Definition premethod_to_method (pre_m : C.premethod) : C.method :=
 C.mkMethod (C.premethod_name pre_m)
            (C.premethod_descriptor pre_m)
            (C.premethod_public pre_m)
            (C.premethod_protected pre_m)
            (C.premethod_private pre_m)
            (C.premethod_abstract pre_m)
            (C.premethod_static pre_m)
            (C.premethod_final pre_m)
            (C.premethod_synchronized pre_m)
            (C.premethod_strict pre_m)
            (match C.premethod_code pre_m with None => None | Some pc => Some (precode_to_code pc) end)
            (C.premethod_annot pre_m).

Fixpoint load_methods (premethods : list C.premethod) (methods : C.MethodList.t) {struct premethods} :=
 match premethods with
 | nil =>
    Some methods
 | pre_m::premethods =>
    let mdesc := (C.premethod_name pre_m, C.premethod_descriptor pre_m) in
    match C.MethodList.lookup methods mdesc with
    | None =>
       load_methods premethods (C.MethodList.update methods mdesc (premethod_to_method pre_m))
    | Some _ => (* duplicate method entries *)
       None
    end
 end.

Definition descriptor_eq_dec : forall (d d':C.descriptor), {d=d'}+{d<>d'}.
intros. destruct (C.Descriptor_as_UOT.compare d d').
 right. apply C.Descriptor_as_UOT.lt_not_eq. apply l.
 left. apply e.
 right. unfold not. intros. symmetry in H. generalize H. apply C.Descriptor_as_UOT.lt_not_eq. apply l.
Save.

Lemma pair_neq : forall (a1 a2:B.Methodname.t) (b1 b2:C.descriptor), (a1,b1)<>(a2,b2) -> a1 <> a2 \/ b1 <> b2.
intros.
destruct (B.Methodname.eq_dec a1 a2); subst; auto.
destruct (descriptor_eq_dec b1 b2); subst; intuition eauto.
Save.

Definition mdesc_eq_dec : forall (d d' : B.Methodname.t * C.descriptor), {d=d'}+{d<>d'}.
decide equality. apply descriptor_eq_dec. apply B.Methodname.eq_dec.
Save.

Lemma load_methods_ok : forall premethods methods methods',
 load_methods premethods methods = Some methods' ->
 forall md m, C.MethodList.lookup methods' md = Some m <->
             (exists pm, m = premethod_to_method pm /\ C.has_premethod premethods md pm /\ C.MethodList.lookup methods md = None)
              \/ C.MethodList.lookup methods md = Some m.
induction premethods; intros; simpl in H.
 (* nil *)
 inversion H. clear H. subst.
 split; intro.
  right. assumption.
  destruct H as [[pm [m_pm [has_pm _]]] | methods'_m].
   inversion has_pm.
   assumption.
 (* cons *)
 destruct (option_dec (C.MethodList.lookup methods (C.premethod_name a, C.premethod_descriptor a))) as [[x lookup_res] | lookup_res]; rewrite lookup_res in H.
  (* duplicate method *)
  discriminate.
  (* not a duplicate *)
  split; intro.
   rewrite (IHpremethods _ _ H) in H0. destruct H0 as [[pm [m_pm [has_pm not_in_methods]]] | methods_md].
    destruct md. destruct (mdesc_eq_dec (C.premethod_name a, C.premethod_descriptor a) (t,d)).
     inversion e. clear e. subst. rewrite C.MethodList.lookup_update in not_in_methods. discriminate.
     left. exists pm. split.
      assumption.
      split.
       destruct a. simpl in *. apply C.has_premethod_cons_2. assumption. apply pair_neq. assumption.
       rewrite C.MethodList.indep_lookup in not_in_methods; assumption.
    destruct md. destruct (mdesc_eq_dec (C.premethod_name a, C.premethod_descriptor a) (t,d)).
     inversion e. clear e. subst. rewrite C.MethodList.lookup_update in methods_md. inversion methods_md. clear methods_md. subst.
      left. exists a. intuition. destruct a. apply C.has_premethod_cons_1.
     right. rewrite C.MethodList.indep_lookup in methods_md; assumption.
   rewrite (IHpremethods _ _ H). destruct H0 as [[pm [m_pm [has_pm md_None]]] | md_m].
    inversion has_pm; subst; simpl in *.
     right. apply C.MethodList.lookup_update.
     left. exists pm. split.
      reflexivity.
      split.
       apply H2.
       rewrite C.MethodList.indep_lookup.
        assumption.
        unfold not. intro. inversion H0. subst. destruct H5 as [X|X]; apply X; reflexivity.
    destruct md. destruct (mdesc_eq_dec (C.premethod_name a, C.premethod_descriptor a) (t,d)).
     inversion e. subst. rewrite lookup_res in md_m. discriminate.
     right. rewrite C.MethodList.indep_lookup; assumption.
Save.

Definition preclass_to_class : C.preclass -> option C.class := fun pre_c =>
  match load_methods (C.preclass_methods pre_c) C.MethodList.empty with
  | None => (* loading the methods failed *)
     None
  | Some methods =>
    Some (C.mkClass (C.preclass_name pre_c)
                    (C.preclass_super_name pre_c)
                    (C.preclass_super_interfaces pre_c)
                    (C.preclass_public pre_c)
                    (C.preclass_final pre_c)
                    (C.preclass_super pre_c)
                    (C.preclass_interface pre_c)
                    (C.preclass_abstract pre_c)
                    methods
                    (C.preclass_fields pre_c)
                    (C.preclass_constantpool pre_c))
  end.

Lemma preclass_to_class_props : forall pc c,
 preclass_to_class pc = Some c ->
   C.class_name c = C.preclass_name pc
 /\C.class_constantpool c = C.preclass_constantpool pc
 /\(forall md m, (exists pm, m = premethod_to_method pm /\ C.has_premethod (C.preclass_methods pc) md pm) <-> C.MethodList.lookup (C.class_methods c) md = Some m)
 /\C.class_interface c = C.preclass_interface pc
 /\C.class_super_class c = C.preclass_super_name pc
 /\C.class_interfaces c = C.preclass_super_interfaces pc.
intros. unfold preclass_to_class in H.
destruct (option_dec (load_methods (C.preclass_methods pc) C.MethodList.empty)) as [[methods load_res] | load_res]; rewrite load_res in H.
 (* load succeeded *)
 inversion H. simpl in *.  intuition.
  destruct H0 as [pm [m_pm has_pm]]. rewrite (load_methods_ok _ _ _ load_res). left. exists pm. intuition. apply C.MethodList.lookup_empty.
  rewrite (load_methods_ok _ _ _ load_res) in H0. destruct H0 as [[pm [m_pm [has_pm _]]] | H0].
   intuition eauto.
   rewrite C.MethodList.lookup_empty in H0. discriminate.
 (* load failed: impossible *)
 discriminate.
Save.

Lemma addition_establishes_invariant_for_class : forall classes pc nm pc_c c,
  Classpool.lookup classes (C.preclass_name pc) = None ->
  nm = C.preclass_name pc ->
  C.preclass_interface pc = false ->
  C.preclass_super_name pc <> None ->
  good_interface_list classes (C.preclass_super_interfaces pc) ->
  good_super_class classes (C.preclass_super_name pc) ->
  preclass_to_class pc = Some pc_c ->
  Classpool.lookup (Classpool.update classes (C.preclass_name pc) pc_c) nm = Some c ->
  class_invariant (Classpool.update classes (C.preclass_name pc) pc_c) nm c.
intros classes pc nm pc_c c not_already_there nm_eq is_class has_super gil gsc pc_to_c lookup. 
rewrite nm_eq in lookup. rewrite nm_eq. rewrite Classpool.lookup_update in lookup. inversion lookup. subst.  
unfold preclass_to_class in pc_to_c.
destruct (option_dec (load_methods (C.preclass_methods pc) C.MethodList.empty))
      as [[methods load_methods_res] | load_methods_res]; rewrite load_methods_res in pc_to_c; [|discriminate].
inversion_clear pc_to_c.
apply mk_class_invariant.
 (* its name matches *)
 reflexivity.
 (* if this has no super class, then its name is j.l.Object *)
 intros. elimtype False. apply has_super. assumption.
 (* it has a good super class and super interface lists *)
 apply mk_class_invariant_class.
  simpl. assumption.
  apply addition_preserves_good_interface_list; assumption.
  apply addition_preserves_good_super_class; assumption.
Save.
Implicit Arguments addition_establishes_invariant_for_class [classes pc nm pc_c c].

Lemma addition_establishes_invariant_for_interface : forall classes pc nm pc_c c,
  Classpool.lookup classes (C.preclass_name pc) = None ->
  nm = C.preclass_name pc ->
  C.preclass_interface pc = true ->
  good_interface_list classes (C.preclass_super_interfaces pc) ->
  C.preclass_super_name pc = Some B.java_lang_Object ->
  preclass_to_class pc = Some pc_c ->
  Classpool.lookup (Classpool.update classes (C.preclass_name pc) pc_c) nm = Some c ->
  class_invariant (Classpool.update classes (C.preclass_name pc) pc_c) nm c.
intros classes pc nm pc_c c not_already_there nm_eq is_interface gil gsc pc_to_c lookup. 
rewrite nm_eq in lookup. rewrite nm_eq. rewrite Classpool.lookup_update in lookup. inversion lookup. subst.
unfold preclass_to_class in pc_to_c.
destruct (option_dec (load_methods (C.preclass_methods pc) C.MethodList.empty))
      as [[methods load_methods_res] | load_methods_res]; rewrite load_methods_res in pc_to_c; [|discriminate].
inversion_clear pc_to_c.
apply mk_class_invariant. 
 reflexivity.
 intros. simpl in H. rewrite H in gsc. discriminate. 
 apply mk_class_invariant_interface.
  simpl. assumption.
  apply addition_preserves_good_interface_list; assumption.
  subst. assumption.
Save.
Implicit Arguments addition_establishes_invariant_for_interface [classes pc nm pc_c c].

Lemma neq_symm : forall (A:Type) (a b:A), a<>b -> b<>a.
unfold not. intros. apply H. symmetry. assumption.
Save.
Implicit Arguments neq_symm [A a b].

Definition preserve_old_classes :=
  fun classes classes' =>
  forall nm c, class_loaded classes nm c ->
               class_loaded classes' nm c.

Lemma preserve_old_classes_id : forall classes,
  preserve_old_classes classes classes.
unfold preserve_old_classes. auto.
Save.

Lemma preserve_old_classes_trans : forall classesA classesB classesC,
  preserve_old_classes classesA classesB ->
  preserve_old_classes classesB classesC ->
  preserve_old_classes classesA classesC.
unfold preserve_old_classes. intuition.
Save.

Lemma addition_preserves_old_classes : forall classes new_nm new_c,
  Classpool.lookup classes new_nm = None ->
  forall nm c, Classpool.lookup classes nm = Some c -> Classpool.lookup (Classpool.update classes new_nm new_c) nm = Some c.
intros. destruct (B.Classname.eq_dec new_nm nm). 
 subst. rewrite H in H0. discriminate.
 rewrite Classpool.indep_lookup; assumption.
Save.

Definition only_add_one := fun classes classes' new_nm p =>
  forall nm c, Classpool.lookup (classpool classes') nm = Some c ->
               ((nm = new_nm /\ Some c = preclass_to_class p)
                \/ (nm <> new_nm /\ Classpool.lookup (classpool classes) nm = Some c)).

Lemma addition_only_adds_one : forall classes new_nm p pc_c,
  preclass_to_class p = Some pc_c ->
  forall nm c, Classpool.lookup (Classpool.update classes new_nm pc_c) nm = Some c -> ((nm = new_nm /\ Some c = preclass_to_class p) \/ (nm <> new_nm /\ Classpool.lookup classes nm = Some c)).
intros. destruct (B.Classname.eq_dec new_nm nm).
 subst. left. intuition. rewrite Classpool.lookup_update in H0. inversion H0. subst. symmetry. assumption.
 right. intuition. rewrite Classpool.indep_lookup in H0; assumption.
Save.

Lemma addition_preserves_Object : forall classes new_nm new_c,
  new_nm <> B.java_lang_Object ->
  (exists c, Classpool.lookup classes B.java_lang_Object = Some c /\ C.class_super_class c = None /\ C.class_interfaces c = nil /\ C.class_interface c = false) ->
  (exists c, Classpool.lookup (Classpool.update classes new_nm new_c) B.java_lang_Object = Some c /\ C.class_super_class c = None /\ C.class_interfaces c = nil /\ C.class_interface c = false).
intros. rewrite Classpool.indep_lookup; assumption.
Save.

Definition add_class : forall classes pre_c,
  C.preclass_name pre_c <> B.java_lang_Object ->
  Classpool.lookup (classpool classes) (C.preclass_name pre_c) = None ->
  (good_interface_list (classpool classes) (C.preclass_super_interfaces pre_c)) ->
  C.preclass_interface pre_c = false ->
  C.preclass_super_name pre_c <> None ->
  good_super_class (classpool classes) (C.preclass_super_name pre_c) ->
  { classes' : cert_classpool, c : C.class |
      preserve_old_classes classes classes'
   /\ only_add_one classes classes' (C.preclass_name pre_c) pre_c
   /\ Classpool.lookup (classpool classes') (C.preclass_name pre_c) = Some c }
  + exn
  :=
  fun classes pre_c not_Object not_already_there gil not_interface no_super gsc =>
  match option_informative (preclass_to_class pre_c) with
  | inleft (exist new_c prec_to_newc) =>
     let classes' := Classpool.update (classpool classes) (C.preclass_name pre_c) new_c in
     let invariant := 
        (fun nm c (c_exists:Classpool.lookup classes' nm = Some c) =>
            match B.Classname.eq_dec nm (C.preclass_name pre_c) with
            | right not_eq =>
                let c_exists_previously := Classpool.indep_lookup_2 _ _ _ _ _ (neq_symm not_eq) c_exists in
                let old_invariant := classpool_invariant classes nm c c_exists_previously in
                  addition_preserves_invariant not_already_there old_invariant
            | left is_eq =>
                addition_establishes_invariant_for_class not_already_there is_eq not_interface no_super gil gsc prec_to_newc c_exists
            end) in
     let Object_exists := addition_preserves_Object _ (C.preclass_name pre_c) new_c not_Object (classpool_Object classes) in
     let P := fun classes' c => preserve_old_classes classes classes' /\ only_add_one classes classes' (C.preclass_name pre_c) pre_c /\ Classpool.lookup (classpool classes') (C.preclass_name pre_c) = Some c in
       inl _ (pack2 P (mk_classpool classes' invariant Object_exists) new_c
               (conj (addition_preserves_old_classes _ _ _ not_already_there)
                     (conj (addition_only_adds_one _ _ _ _ prec_to_newc)
                           (Classpool.lookup_update _ _ _))))
  | inright _ =>
     (* actual class loading failed *)
     inr _ errClassFormat
  end.

Definition add_interface : forall classes pre_c,
  C.preclass_name pre_c <> B.java_lang_Object ->
  Classpool.lookup (classpool classes) (C.preclass_name pre_c) = None ->
  (good_interface_list (classpool classes) (C.preclass_super_interfaces pre_c)) ->
  C.preclass_interface pre_c = true ->
  C.preclass_super_name pre_c = Some B.java_lang_Object ->
  { classes' : cert_classpool, c : C.class |
      preserve_old_classes classes classes'
   /\ only_add_one classes classes' (C.preclass_name pre_c) pre_c
   /\ Classpool.lookup (classpool classes') (C.preclass_name pre_c) = Some c }
  + exn
  :=
  fun classes pre_c not_Object not_already_there gil is_interface gsc =>
  match option_informative (preclass_to_class pre_c) with
  | inleft (exist new_c prec_to_newc) =>
     let classes' := Classpool.update (classpool classes) (C.preclass_name pre_c) new_c in
     let invariant := 
      (fun nm c (c_exists:Classpool.lookup classes' nm = Some c) =>
         match B.Classname.eq_dec nm (C.preclass_name pre_c) with
         | right not_eq =>
             let c_exists_previously := Classpool.indep_lookup_2 _ _ _ _ _ (neq_symm not_eq) c_exists in
             let old_invariant := classpool_invariant classes nm c c_exists_previously in
               addition_preserves_invariant not_already_there old_invariant
         | left is_eq =>
             addition_establishes_invariant_for_interface not_already_there is_eq is_interface gil gsc prec_to_newc c_exists
         end) in
     let Object_exists := addition_preserves_Object _ (C.preclass_name pre_c) new_c not_Object (classpool_Object classes) in
     let P := fun classes' c => preserve_old_classes classes classes'
                                /\ only_add_one classes classes' (C.preclass_name pre_c) pre_c
                                /\ Classpool.lookup (classpool classes') (C.preclass_name pre_c) = Some c in
       inl _ (pack2 P (mk_classpool classes' invariant Object_exists) new_c
               (conj (addition_preserves_old_classes _ _ _ not_already_there)
                     (conj (addition_only_adds_one _ _ _ _ prec_to_newc)
                           (Classpool.lookup_update _ _ _))))
  | inright _ =>
     inr _ errClassFormat
  end.

Implicit Arguments add_class [classes pre_c].
Implicit Arguments add_interface [classes pre_c].

(* Loading classes *)

Definition only_add_from_preclasses := fun classes classes' preclasses =>
  forall nm c, class_loaded classes' nm c ->
               ((exists pc, preclass_to_class pc = Some c /\ Preclasspool.lookup preclasses nm = Some pc /\ forall c', ~class_loaded classes nm c')
                \/ class_loaded classes nm c).

Inductive load_type (A:Type) (P:cert_classpool -> A -> Prop) (classes:cert_classpool) (preclasses:Preclasspool.t) : Type :=
| load_ok : forall classes', preserve_old_classes classes classes' -> only_add_from_preclasses classes classes' preclasses -> forall a, P classes' a -> load_type A P classes preclasses
| load_err : forall classes', preserve_old_classes classes classes' -> only_add_from_preclasses classes classes' preclasses -> exn -> load_type A P classes preclasses.

Arguments Scope load_type [type_scope type_scope].

Notation "{LOAD c , p ~~> c2 & x : A | Q }" := (load_type A (fun (c2:cert_classpool) (x:A) => Q) c p) (at level 0, x at level 99, c2 at level 99) : type_scope.

Implicit Arguments load_ok [A classes preclasses classes'].
Implicit Arguments load_err [A classes preclasses classes'].

Implicit Arguments gil_cons [classes i_nm rest i].
Implicit Arguments gsc_step [classes super_c super_name].


Lemma cert_classpool_gives_gil : forall classes nm c,
  Classpool.lookup (classpool classes) nm = Some c -> good_interface_list (classpool classes) (C.class_interfaces c).
intros. destruct classes. 
simpl in * |- *. case (classpool_invariant0 _ _ H). intros. destruct H2; assumption.
Save.
Implicit Arguments cert_classpool_gives_gil [classes nm c].

Lemma cert_classpool_gives_gsc : forall classes nm c,
  Classpool.lookup (classpool classes) nm = Some c -> C.class_interface c = false -> good_super_class (classpool classes) (C.class_super_class c).
intros. destruct classes. simpl in * |- *.
generalize H0. case (classpool_invariant0 _ _ H). intros. destruct H3. 
 assumption.
 rewrite H4 in H3. discriminate.
Save.
Implicit Arguments cert_classpool_gives_gsc [classes nm c].

Lemma preservation_preserves_gil : forall classes classes' l,
  preserve_old_classes classes classes' -> good_interface_list (classpool classes) l -> good_interface_list (classpool classes') l.
unfold preserve_old_classes. unfold class_loaded. intros.
induction H0; eauto using gil_nil, gil_cons.
Save.
Implicit Arguments preservation_preserves_gil [classes classes' l].

Lemma compose_preserved : forall classes classes' classes'',
  preserve_old_classes classes classes' -> preserve_old_classes classes' classes'' -> preserve_old_classes classes classes''.
unfold preserve_old_classes. auto. 
Save.
Implicit Arguments compose_preserved [classes classes' classes''].

Implicit Arguments option_eq_dec [A].

Lemma switch_names : forall classes nm1 nm2 c, nm2 = nm1 -> Classpool.lookup classes nm1 = c -> Classpool.lookup classes nm2 = c.
intros. rewrite H. assumption.
Save.
Implicit Arguments switch_names [classes nm1 nm2 c].

Lemma switch_prenames : forall classes nm1 nm2 c, nm2 = nm1 -> Preclasspool.lookup classes nm1 = c -> Preclasspool.lookup classes nm2 = c.
intros. rewrite H. assumption.
Save.
Implicit Arguments switch_prenames [classes nm1 nm2 c].

Lemma switch_gsc : forall classes l l', good_super_class classes l -> l' = l -> good_super_class classes l'.
intros. rewrite H0. assumption.
Save.
Implicit Arguments switch_gsc [classes l l'].

Lemma only_add_from_preclasses_implies_not_already_there : forall classes classes' preclasses nm,
  only_add_from_preclasses classes classes' (Preclasspool.remove nm preclasses) ->
  Classpool.lookup (classpool classes) nm = None ->
  Classpool.lookup (classpool classes') nm = None.
unfold only_add_from_preclasses. intros. 
destruct (option_dec (Classpool.lookup (classpool classes') nm)).
 destruct H1. destruct (H _ _ H1) as [[pc [pc2c [pc_lookup _]]]|loaded]. 
  rewrite Preclasspool.remove_lookup in pc_lookup. congruence.  
  congruence.
 assumption.
Save.
Implicit Arguments only_add_from_preclasses_implies_not_already_there [classes classes' preclasses nm].

Lemma only_add_id : forall classes preclasses, only_add_from_preclasses classes classes preclasses.
unfold only_add_from_preclasses. auto. 
Save.

Lemma compose_only_add : forall classes classes' classes'' preclasses,
  preserve_old_classes classes classes' ->
  only_add_from_preclasses classes classes' preclasses ->
  only_add_from_preclasses classes' classes'' preclasses ->
  only_add_from_preclasses classes classes'' preclasses.
unfold only_add_from_preclasses. intros. 
destruct (H1 _ _ H2) as [[pc [pc2c [pc_lookup not_there]]]|loaded].
 left. exists pc. intuition. eapply not_there. apply (H _ _ H3).
 exact (H0 _ _ loaded).
Save.
Implicit Arguments compose_only_add [classes classes' classes'' preclasses].

Lemma lift_only_add : forall classes classes' preclasses nm,
  only_add_from_preclasses classes classes' (Preclasspool.remove nm preclasses) ->
  only_add_from_preclasses classes classes' preclasses.
unfold only_add_from_preclasses. intros. 
destruct (H _ _ H0). 
 left. destruct H1. destruct H1. destruct H2. exists x. split.
  assumption.
  split.
   eapply Preclasspool.remove_lookup_3. apply H2.
   apply H3. 
 right. assumption. 
Save.
Implicit Arguments lift_only_add [classes classes' preclasses nm].

Lemma only_add_one_preserves_only_add_from_preclasses : forall classes classes' classes'' preclasses p,
  only_add_one classes' classes'' (C.preclass_name p) p ->
  Classpool.lookup (classpool classes') (C.preclass_name p) = None ->
  preserve_old_classes classes classes' ->
  only_add_from_preclasses classes classes' (Preclasspool.remove (C.preclass_name p) preclasses) ->
  Preclasspool.lookup preclasses (C.preclass_name p) = Some p ->
  only_add_from_preclasses classes classes'' preclasses.
unfold only_add_one. unfold only_add_from_preclasses. intros.
destruct (H _ _ H4). 
 destruct H5. subst. left. exists p. split; [|split]; auto.
  unfold not. intros. rewrite (H1 _ _ H5) in H0. discriminate.
 destruct H5. apply (lift_only_add H2). assumption.
Save.
Implicit Arguments only_add_one_preserves_only_add_from_preclasses [classes classes' classes'' preclasses p].

Fixpoint load_interfaces (preclasses:Preclasspool.t)
                         (load_and_resolve_aux:forall (target:B.Classname.t) classes, {LOAD classes, preclasses ~~> classes' & c : C.class | Classpool.lookup (classpool classes') target = Some c })
                         (l:list B.Classname.t)
                         (classes:cert_classpool) {struct l}
                       : {LOAD classes, preclasses ~~> classes' & t : unit | good_interface_list (classpool classes') l} :=
  match l as l0 return {LOAD classes, preclasses ~~> classes' & t : unit | good_interface_list (classpool classes') l0 } with
  | nil        =>
     let P := fun classes' t => good_interface_list (classpool classes') nil in
      load_ok P (fun _ _ x => x) (only_add_id classes preclasses) tt (gil_nil (classpool classes))
  | i_nm::rest =>
     let P := fun classes' t => good_interface_list (classpool classes') (i_nm::rest) in
      match load_and_resolve_aux i_nm classes with
      | load_ok classes' preserved only_add c c_exists =>
         match bool_informative (C.class_interface c) with
         | left is_interface =>
            match load_interfaces preclasses load_and_resolve_aux rest classes' with
            | load_ok classes'' preserved' only_add' tt gil =>
               let c_exists' := preserved' _ _ c_exists in
               let new_gil := gil_cons c_exists' is_interface (cert_classpool_gives_gil c_exists') gil in
                (* FIXME: check access permissions *)
                load_ok P (compose_preserved preserved preserved') (compose_only_add preserved only_add only_add') tt new_gil
            | load_err classes'' preserved' only_add' e =>
               load_err P (compose_preserved preserved preserved') (compose_only_add preserved only_add only_add') e
            end
         | right _ =>
            load_err P preserved only_add errIncompatibleClassChange
         end
      | load_err classes' preserved only_add e =>
         load_err P preserved only_add e
      end
   end.

Fixpoint load_and_resolve_aux
  (target:B.Classname.t)
  (preclasses:Preclasspool.t)
  (PI:Preclasspool.wf_removals preclasses)
  (classes:cert_classpool) {struct PI}
  : {LOAD classes, preclasses ~~> classes' & c : C.class | Classpool.lookup (classpool classes') target = Some c }
:=
  let P := fun classes' c => Classpool.lookup (classpool classes') target = Some c in
  match Classpool.lookup_informative (classpool classes) target with
  | inleft (exist c c_exists) => (* class is already there *)
     load_ok P (fun _ _ x => x) (only_add_id classes preclasses) c c_exists
  | inright target_not_in_classes =>
     (* Otherwise, try to load it *)
     match Preclasspool.lookup_informative preclasses target with
     | inleft (exist p p_exists) =>
        match B.Classname.eq_dec (C.preclass_name p) B.java_lang_Object with
        | right not_Object =>
          match B.Classname.eq_dec target (C.preclass_name p) with
          | left names_eq =>
             (* Do some renaming now that we know that the two names are equal *)
             let p_exists := switch_prenames (sym_eq names_eq) p_exists in
             let target_not_in_classes := switch_names (sym_eq names_eq) target_not_in_classes in

             (* Arrange the recursive calls *)
             let preclasses := Preclasspool.remove (C.preclass_name p) preclasses in
             let P' := Preclasspool.wf_removals_inv p_exists PI in
             let load_and_resolve_aux := fun target => load_and_resolve_aux target preclasses P' in

             (* Now start doing stuff. First, resolve the references to super interfaces *)
             match load_interfaces preclasses load_and_resolve_aux (C.preclass_super_interfaces p) classes with
             | load_ok classes' preserved only_add tt gil =>
                (* Now check whether the current class is a real class or an interface *)
                match bool_informative (C.preclass_interface p) with
                | left is_interface =>
                   (* This is an interface, so we just check that the super class is just java.lang.Object *)
                   match option_eq_dec B.Classname.eq_dec (C.preclass_super_name p) (Some B.java_lang_Object) with
                   | left super_ok =>
                      let not_there := only_add_from_preclasses_implies_not_already_there only_add target_not_in_classes in
                      match add_interface not_Object not_there gil is_interface super_ok with
                      | inl (pack2 classes'' c (conj preserved' (conj only_add_one c_exists))) =>
                         let only_add' := only_add_one_preserves_only_add_from_preclasses only_add_one not_there preserved only_add p_exists in
                         load_ok P (compose_preserved preserved preserved') only_add' c (switch_names names_eq c_exists)
                      | inr e =>
                         load_err P preserved (lift_only_add only_add) e
                      end
                   | right _ =>
                      load_err P preserved (lift_only_add only_add) errClassFormat
                   end
                | right is_class =>
                   (* This is a class, so we must load the super class, if it has one *)
                   match option_informative (C.preclass_super_name p) with
                   | inleft (exist s_nm H) =>
                      (* This class has a super class, so we try to load it *)
                      match load_and_resolve_aux s_nm classes' with
                      | load_ok classes'' preserved' only_add' sc sc_exists =>
                         (* Make sure that it is a class and not an interface *)
                         (* FIXME: check access permissions *)
                         match bool_informative (C.class_interface sc) with
                         | right sc_is_class =>
                           let gil := preservation_preserves_gil preserved' gil in
                           let old_gsc := cert_classpool_gives_gsc sc_exists sc_is_class in
                           let gsc := gsc_step sc_exists sc_is_class old_gsc in
                           let only_add'' := compose_only_add preserved only_add only_add' in
                           let not_there := only_add_from_preclasses_implies_not_already_there only_add'' target_not_in_classes in
                             match add_class not_Object not_there gil is_class (Some_isnt_None H) (switch_gsc gsc H) with
                             | inl (pack2 classes''' c (conj preserved'' (conj only_add_one c_exists))) =>
                                let preserved''' := compose_preserved (compose_preserved preserved preserved') preserved'' in
                                let only_add''' := only_add_one_preserves_only_add_from_preclasses only_add_one not_there (compose_preserved preserved preserved') only_add'' p_exists in
                                load_ok P preserved''' only_add''' c (switch_names names_eq c_exists)
                             | inr e =>
                                load_err P (compose_preserved preserved preserved') (lift_only_add (compose_only_add preserved only_add only_add')) e
                             end
                         | left _ =>
                            load_err P (compose_preserved preserved preserved') (lift_only_add (compose_only_add preserved only_add only_add')) errIncompatibleClassChange
                         end
                      | load_err classes'' preserved' only_add' e =>
                         load_err P (compose_preserved preserved preserved') (lift_only_add (compose_only_add preserved only_add only_add')) e
                      end
                    (* No super class *)
                   | inright H => 
                      (* Only java.lang.Object has no super class, and we have already established that this is not it *)
                      load_err P preserved (lift_only_add only_add) errClassFormat
                   end
                end
             | load_err classes' preserved only_add e =>
                load_err P preserved (lift_only_add only_add) e
             end
          | right _ =>
             load_err P (fun _ _ x => x) (only_add_id classes preclasses) errNoClassDefFound
          end
        | left _ =>
           load_err P (fun _ _ x => x) (only_add_id classes preclasses) errClassFormat
        end
     | inright _ =>
        load_err P (fun _ _ x => x) (only_add_id classes preclasses) errNoClassDefFound (* FIXME: this sometimes misreports errClassCircularity *)
     end
  end.

Definition check_class_access : B.Classname.t -> C.class -> option exn :=
  fun caller target => None. (*if C.class_public target then None else Some errIllegalAccess.*)
(* FIXME: should also check that they are in the same package *)

Definition resolve_class : forall (caller target:B.Classname.t) classes preclasses,
  {LOAD classes, preclasses ~~> classes' & c : C.class | class_loaded classes' target c }
  :=
  fun caller target classes preclasses =>
  let P := fun classes' c => Classpool.lookup (classpool classes') target = Some c in
  match load_and_resolve_aux target preclasses (Preclasspool.all_wf_removals preclasses) classes with
  | load_ok classes' preserved only_add c c_exists =>
     match check_class_access caller c with
     | Some e =>
        load_err P preserved only_add e
     | None =>
        load_ok P preserved only_add c c_exists
     end
  | load_err classes' preserved only_add e =>
     load_err P preserved only_add e
  end.

(* Utility for easier super class access *)

Inductive super_class_chain (classes:cert_classpool) : option B.Classname.t -> Prop :=
| class_chain_end  : super_class_chain classes None
| class_chain_step : forall nm c,
   Classpool.lookup (classpool classes) nm = Some c ->
   C.class_interface c = false ->
   (forall c',
     Classpool.lookup (classpool classes) nm = Some c' ->
     super_class_chain classes (C.class_super_class c')) ->
   super_class_chain classes (Some nm).

Scheme super_class_chain_induction := Induction for super_class_chain Sort Prop.

(* Inversion lemmas for super_class_chain *)
Lemma scc_None : forall classes (ssc:super_class_chain classes None),
  ssc = class_chain_end classes.
intros. 
pose (t:=None (A:=B.Classname.t)).
change (class_chain_end classes) with (eq_ind t (super_class_chain classes) (class_chain_end classes) None (refl_equal t)).
set (e:=refl_equal t : t = None). generalize e. 
dependent inversion ssc. 
intro. pattern e0. apply K_dec_set. decide equality. apply B.Classname.eq_dec. reflexivity.
Save.

Lemma scc_Some : forall classes nm (ssc:super_class_chain classes (Some nm)),
  exists c, exists c_exists, exists c_class, exists s,
    ssc = class_chain_step classes nm c c_exists c_class s.
intros. 
pose (t:=Some nm).
change (ex (fun c => ex (fun c_exists => ex (fun c_class => ex (fun s =>
         ssc = class_chain_step classes nm c c_exists c_class s)))))
  with (ex (fun c => ex (fun c_exists => ex (fun c_class => ex (fun s =>
         ssc = (eq_ind t (super_class_chain classes) (class_chain_step classes nm c c_exists c_class s) (Some nm) (refl_equal t))))))).
set (e:=refl_equal t : t = Some nm). generalize e. 
dependent inversion ssc.
intros. pattern e2. apply K_dec_set. decide equality. apply B.Classname.eq_dec. 
exists c. exists e0. exists e1. exists s. reflexivity.
Save.

Definition super_class_chain_inv : forall classes nm c o_nm,
  Classpool.lookup (classpool classes) nm = Some c ->
  o_nm = Some nm ->
  super_class_chain classes o_nm ->
  super_class_chain classes (C.class_super_class c)
  :=
fun (classes : cert_classpool_aux) (nm : Classpool.key)
  (c : Classpool.object) (o_nm : option Classpool.key)
  (H : Classpool.lookup (classpool classes) nm = Some c)
  (H0 : o_nm = Some nm) (H1 : super_class_chain classes o_nm) =>
match
  H1 in (super_class_chain _ o)
  return (o = Some nm -> super_class_chain classes (C.class_super_class c))
with
| class_chain_end =>
    fun H2 : None = Some nm =>
    let H3 :=
      eq_ind None
        (fun ee : option Classpool.key =>
         match ee with
         | Some _ => False
         | None => True
         end) I (Some nm) H2 in
    False_ind (super_class_chain classes (C.class_super_class c)) H3
| class_chain_step nm0 c0 _ _ H2 =>
    fun H3 : Some nm0 = Some nm =>
    let H4 :=
      f_equal
        (fun e : option Classpool.key =>
         match e with
         | Some k => k
         | None => nm0
         end) H3 in
    let H5 :=
      eq_ind_r
        (fun nm1 : Classpool.key =>
         Classpool.lookup (classpool classes) nm1 = Some c) H H4 in
    H2 c H5
end H0.
Implicit Arguments super_class_chain_inv [classes nm c o_nm].

Lemma super_class_chain_not_not_there_old : forall classes nm o_nm,
  o_nm = Some nm ->
  super_class_chain classes o_nm ->
  ~(Classpool.lookup (classpool classes) nm = None).
intros. destruct H0.
 discriminate.
 injection H. intro. rewrite <- H3. unfold not. intro. rewrite H0 in H4. discriminate.
Defined.
Implicit Arguments super_class_chain_not_not_there_old [classes nm o_nm].

Lemma super_class_chain_not_not_there : forall classes nm o_nm,
  o_nm = Some nm ->
  super_class_chain classes o_nm ->
  ~(~(exists c, class_loaded classes nm c)).
intros. destruct H0.
 discriminate.
 injection H. intro. rewrite <- H3. unfold not. intro. apply H4. unfold class_loaded. rewrite H0. eauto.
Defined.
Implicit Arguments super_class_chain_not_not_there [classes nm o_nm].

Lemma scc_gives_class : forall classes o_nm nm c,
  o_nm = Some nm ->
  super_class_chain classes o_nm ->
  Classpool.lookup (classpool classes) nm = Some c ->
  C.class_interface c = false.
intros. destruct H0.
 discriminate.
 inversion H. subst. rewrite H1 in H0. inversion H0. subst. assumption.
Save.
Implicit Arguments scc_gives_class [classes o_nm nm c]. 

Lemma gsc_implies_scc : forall classes nm, good_super_class (classpool classes) nm -> super_class_chain classes nm.
intros. induction H. 
 apply class_chain_end.
 eapply class_chain_step; eauto.
  intros. rewrite H in H2. inversion H2. rewrite <- H4. assumption.
Save.
Implicit Arguments gsc_implies_scc [classes nm].

Lemma scc_implies_gsc : forall classes nm, super_class_chain classes nm -> good_super_class (classpool classes) nm.
intros classes nm H. induction H; eauto using gsc_top, gsc_step.
Save.
Implicit Arguments scc_implies_gsc [classes nm].

Lemma cert_classpool_gives_scc : forall classes nm c,
  Classpool.lookup (classpool classes) nm = Some c ->
  C.class_interface c = false ->
  super_class_chain classes (C.class_super_class c).
intuition eauto using gsc_implies_scc, cert_classpool_gives_gsc.
Save.
Implicit Arguments cert_classpool_gives_scc [classes nm c].

(* and again for super interfaces *)

Inductive good_interface_list2 : cert_classpool -> list B.Classname.t -> Prop :=
| gil2_nil : forall classes,
   good_interface_list2 classes nil
| gil2_cons : forall classes i_nm rest i,
   class_loaded classes i_nm i ->
   C.class_interface i = true ->
   (forall c',
     class_loaded classes i_nm c' ->
     good_interface_list2 classes (C.class_interfaces c')) ->
   good_interface_list2 classes rest ->
   good_interface_list2 classes (i_nm::rest).

Definition good_interface_list2_inv_1 : forall classes l i_nm rest i,
  good_interface_list2 classes l ->
  l = i_nm::rest ->
  Classpool.lookup (classpool classes) i_nm = Some i ->
  good_interface_list2 classes (C.class_interfaces i) :=
 fun classes t0 i_nm rest i H H0 H1 =>
  match
   H in (good_interface_list2 c l)
     return
     (l = i_nm :: rest ->
       Classpool.lookup (classpool c) i_nm = Some i ->
       good_interface_list2 c (C.class_interfaces i))
    with
    | gil2_nil classes0 =>
      fun H2 _ =>
        let H4 := eq_ind nil (fun e => match e with nil => True | _ :: _ => False end) I (i_nm :: rest) H2
          in
          False_ind (good_interface_list2 classes0 (C.class_interfaces i)) H4
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
            (fun e : list B.Classname.t =>
              match e with
                | nil => rest0
                | _ :: l => l
              end) H6 in
            fun H10 : i_nm0 = i_nm =>
              let H11 :=
                eq_ind_r
                (fun i_nm1 : B.Classname.t =>
                  class_loaded classes0 i_nm1 i0 ->
                  (forall c' : Classpool.object,
                    class_loaded classes0 i_nm1 c' ->
                    good_interface_list2 classes0 (C.class_interfaces c')) ->
                  i_nm1 :: rest0 = i_nm :: rest -> class_loaded classes0 i_nm1 i)
                (fun (_ : class_loaded classes0 i_nm i0)
                  (_ : forall c' : Classpool.object,
                    class_loaded classes0 i_nm c' ->
                    good_interface_list2 classes0 (C.class_interfaces c'))
                  (H13 : i_nm :: rest0 = i_nm :: rest) =>
                  let H14 :=
                    eq_ind_r
                    (fun rest1 : list B.Classname.t =>
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
fun (classes : cert_classpool) (l : list B.Classname.t)
  (i_nm : B.Classname.t) (rest : list B.Classname.t)
  (H : good_interface_list2 classes l) (H0 : l = i_nm :: rest) =>
match
  H in (good_interface_list2 c l0)
  return (l0 = i_nm :: rest -> good_interface_list2 c rest)
with
| gil2_nil classes0 =>
    fun H1 : nil = i_nm :: rest =>
    let H2 :=
      eq_ind nil
        (fun e : list B.Classname.t =>
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
          (fun e : list B.Classname.t =>
           match e with
           | nil => i_nm0
           | t0 :: _ => t0
           end) H5 in
      (let H7 :=
         f_equal
           (fun e : list B.Classname.t =>
            match e with
            | nil => rest0
            | _ :: l0 => l0
            end) H5 in
       fun _ : i_nm0 = i_nm => H7) H6 in
    eq_ind rest0
      (fun rest1 : list B.Classname.t => good_interface_list2 classes0 rest1)
      H4 rest H6
end H0.
Implicit Arguments good_interface_list2_inv_2 [classes l i_nm rest].

Lemma good_interface_list2_not_not_there : forall classes t i_nm rest,
  good_interface_list2 classes t ->
  t = i_nm::rest ->
  ~(~(exists c, class_loaded classes i_nm c)).
unfold not. intros. subst. inversion H. eauto.
Save.

Lemma good_interface_list2_inv_3 : forall classes t i_nm rest,
  good_interface_list2 classes t ->
  t = i_nm::rest ->
  ~(Classpool.lookup (classpool classes) i_nm = None).
intros. destruct H. 
 discriminate.
 replace i_nm with i_nm0.
  unfold not. intro. rewrite H in H4. discriminate.
  injection H0. trivial.
Save.

Lemma gil2_gives_interface : forall classes t i_nm rest i,
  good_interface_list2 classes t ->
  t = i_nm::rest ->
  Classpool.lookup (classpool classes) i_nm = Some i ->
  C.class_interface i = true.
intros. destruct H.
 discriminate.
 inversion H0. subst. rewrite H in H1. inversion H1. subst. assumption.
Save. 

Scheme good_interface_list2_induction := Induction for good_interface_list2 Sort Prop.

Lemma gil2_inv_nil : forall classes (gil:good_interface_list2 classes nil),
  gil = gil2_nil classes.
intros.
pose (t:=nil (A:=B.Classname.t)).
change (gil2_nil classes) with (eq_ind t (good_interface_list2 classes) (gil2_nil classes) nil (refl_equal t)).
set (e:=refl_equal t : t = nil). generalize e.
dependent inversion gil.
intro. pattern e0. apply K_dec_set. decide equality. apply B.Classname.eq_dec. reflexivity.
Save.
Implicit Arguments gil2_inv_nil [classes].

Lemma gil2_inv_cons : forall classes i_nm rest (gil:good_interface_list2 classes (i_nm::rest)),
  exists i, exists i_exists, exists i_interface, exists go_up, exists go_along,
   gil = gil2_cons classes i_nm rest i i_exists i_interface go_up go_along.
intros.
pose (t:=i_nm::rest).
change (ex (fun i => ex (fun i_exists => ex (fun i_interface => ex (fun go_up => ex (fun go_along =>
          gil = gil2_cons classes i_nm rest i i_exists i_interface go_up go_along))))))
  with (ex (fun i => ex (fun i_exists => ex (fun i_interface => ex (fun go_up => ex (fun go_along =>
          gil = (eq_ind t (good_interface_list2 classes) (gil2_cons classes i_nm rest i i_exists i_interface go_up go_along) (i_nm::rest) (refl_equal t)))))))).
set (e:=refl_equal t : t = i_nm::rest). generalize e.
dependent inversion gil.
intro. pattern e1. apply K_dec_set. decide equality. apply B.Classname.eq_dec. 
exists i. exists c. exists e0. exists g. exists g0. reflexivity.
Save.
Implicit Arguments gil2_inv_cons [classes i_nm rest].

Lemma gil_implies_gil2 : forall classes l,
  good_interface_list (classpool classes) l ->
  good_interface_list2 classes l.
intros.
pose (clses:=classpool classes). set (e:=refl_equal clses: classpool classes = clses). 
generalize e. clear e. intro. rewrite e in H.
induction H; subst.
 apply gil2_nil.
 eapply gil2_cons; unfold class_loaded; eauto.
  intros. rewrite H in H3. inversion H3. subst. auto.
Save.
Implicit Arguments gil_implies_gil2 [classes l].

Lemma cert_classpool_gives_gil2 : forall classes nm c,
  class_loaded classes nm c ->
  good_interface_list2 classes (C.class_interfaces c).
intros. unfold class_loaded in *. eauto using cert_classpool_gives_gil, gil_implies_gil2.
Save.
Implicit Arguments cert_classpool_gives_gil2 [classes nm c].

(* Preservation of resolvability *)

Definition preserve_id := fun classes =>
  fun (nm:B.Classname.t) (c:C.class) (x:Classpool.lookup (classpool classes) nm = Some c) => x.

Lemma eq_dec_eq : forall (A:Type) (eq_dec:forall (a b:A), {a=b}+{a<>b}) (a b:A), a=b -> exists p:a=b, eq_dec a b = left _ p.
intros. destruct (eq_dec a b). 
 exists e. reflexivity.
 contradiction.
Save.

Lemma eq_dec_neq : forall (A:Type) (eq_dec:forall (a b:A), {a=b}+{a<>b}) (a b:A), a<>b -> exists p:a<>b, eq_dec a b = right _ p.
intros. destruct (eq_dec a b).
 contradiction.
 exists n. reflexivity.
Save.

Lemma sumbool_dec : forall (P Q:Prop) (dec:{P}+{Q}),
  (exists p, dec = left _ p)\/(exists p, dec = right _ p).
intros. destruct dec.
 left. exists p. reflexivity.
 right. exists q. reflexivity.
Save.
Implicit Arguments sumbool_dec [P Q].

Lemma sumor_dec: forall (A:Type) (P:Prop) (dec:A+{P}),
  (exists p, dec = inleft _ p)\/(exists p, dec = inright _ p).
intros. destruct dec.
 left. exists a. reflexivity.
 right. exists p. reflexivity.
Save.
Implicit Arguments sumor_dec [A P].

Lemma loader_dec : forall (A:Type) (P:cert_classpool -> A -> Prop) preclasses classes (f:{LOAD classes,preclasses ~~> classes' & x : A | P classes' x}),
    (exists classes', exists preserved : preserve_old_classes classes classes', exists only_add, exists a, exists H, f = load_ok _ preserved only_add a H)
 \/ (exists classes', exists preserved : preserve_old_classes classes classes', exists only_add, exists e, f = load_err _ preserved only_add e).
intros. destruct f.
 left. exists classes'. exists p. exists o. exists a. exists p0. reflexivity.
 right. exists classes'. exists p. exists o. exists e. reflexivity.
Save.
Implicit Arguments loader_dec [A P preclasses classes].

Definition preclass_incl := fun preclasses preclasses' =>
  forall nm p, Preclasspool.lookup preclasses nm = Some p -> Preclasspool.lookup preclasses' nm = Some p.

Lemma preclass_incl_remove : forall preclasses x,
  preclass_incl (Preclasspool.remove x preclasses) preclasses.
unfold preclass_incl.
intros. eapply Preclasspool.remove_lookup_3. apply H.
Save.

Lemma preclass_incl_trans : forall preclasses preclasses' preclasses'',
  preclass_incl preclasses preclasses' ->
  preclass_incl preclasses' preclasses'' ->
  preclass_incl preclasses preclasses''.
unfold preclass_incl. auto.
Save.

Lemma load_interfaces_null :
  forall l preclasses preclasses' load_and_resolve_aux_rec
    classesA classesA' classesB (preserved:preserve_old_classes classesA classesA') only_add gil,
  load_interfaces preclasses load_and_resolve_aux_rec l classesA = load_ok _ preserved only_add tt gil ->
  preserve_old_classes classesA classesB ->
  preclass_incl preclasses preclasses' ->
  only_add_from_preclasses classesA classesB preclasses' ->
  (forall a classesA classesB classesA' (p:preserve_old_classes classesA classesA') o c c_ex,
      load_and_resolve_aux_rec a classesA = load_ok _ p o c c_ex ->
      preserve_old_classes classesA classesB ->
      preclass_incl preclasses preclasses' ->
      only_add_from_preclasses classesA classesB preclasses' ->
      (exists c', Classpool.lookup (classpool classesB) a = Some c') ->
         preserve_old_classes classesA' classesB
      /\ only_add_from_preclasses classesA' classesB preclasses') ->
  holds_for_list (fun nm => exists c, Classpool.lookup (classpool classesB) nm = Some c) l ->
     preserve_old_classes classesA' classesB
  /\ only_add_from_preclasses classesA' classesB preclasses'.
intros l preclasses preclasses' load_and_resolve_aux_rec. induction l; intros; simpl in *.

(* empty list *)
inversion H. subst. split; trivial.

(* step case *)
destruct (loader_dec (P:=fun classes c => Classpool.lookup (classpool classes) a = Some c)
                     (load_and_resolve_aux_rec a classesA));
 destruct H5; destruct H5; destruct H5; destruct H5.
 (* Load succeeded *)
 destruct H5. rewrite H5 in H.
 destruct (bool_informative (C.class_interface x2)).
  (* It was an interface *)
  destruct (loader_dec (P:=fun classes t => good_interface_list (classpool classes) l)
                       (load_interfaces preclasses load_and_resolve_aux_rec l x));
    destruct H6; destruct H6; destruct H6; destruct H6.
   (* loading the rest succeeded *)
   destruct H6. rewrite H6 in H. 
   destruct x7. 
   inversion H. subst. 
   inversion H4. subst. 
   destruct (H3 _ _ _ _ _ _ _ _ H5 H0 H1 H2 H9).
   apply (IHl _ _ _ _ _ _ H6 H7 H1 H8 H3 H10).
   (* loading the rest failed *)
   rewrite H6 in H. discriminate.
  (* It wasn't an interface *)
  discriminate.
 (* Load failed *)
 rewrite H5 in H. discriminate.
Save.

Lemma class_exists_implies_interfaces_exist : forall classes nm pc,
  (exists pc_c,
    preclass_to_class pc = Some pc_c
    /\ Classpool.lookup (classpool classes) nm = Some pc_c) ->
  holds_for_list (fun nm' => exists c', Classpool.lookup (classpool classes) nm' = Some c') (C.preclass_super_interfaces pc).
intros. destruct classes. simpl in H.
destruct H as [pc_c [pc_pcc lookup]].
unfold preclass_to_class in pc_pcc.
destruct (option_dec (load_methods (C.preclass_methods pc) C.MethodList.empty)) as [[methods load_res] | load_res]; rewrite load_res in pc_pcc; [|discriminate].
inversion pc_pcc. subst. clear pc_pcc.
pose (B:=classpool_invariant0 _ _ lookup). inversion B.
subst. clear B. inversion H1; subst; clear H1 lookup; simpl in *; (induction (C.preclass_super_interfaces pc);
 [ apply holds_for_nil
 | inversion H2; subst; apply holds_for_cons;[ exists i; assumption | auto ]]).
Save.

Lemma class_exists_implies_super_class_exists : forall classes nm pc sc_nm,
  (exists pc_c,
    preclass_to_class pc = Some pc_c
    /\ Classpool.lookup (classpool classes) nm = Some pc_c) ->
  C.preclass_super_name pc = Some sc_nm ->
  C.preclass_interface pc = false ->
  exists sc, Classpool.lookup (classpool classes) sc_nm = Some sc.
intros. destruct classes. simpl in H.
destruct H as [pc_c [pc_pcc lookup]].
unfold preclass_to_class in pc_pcc.
destruct (option_dec (load_methods (C.preclass_methods pc) C.MethodList.empty)) as [[methods load_res] | load_res]; rewrite load_res in pc_pcc; [|discriminate].
inversion pc_pcc. subst. clear pc_pcc.
pose (B:=classpool_invariant0 _ _ lookup). inversion B.
subst. clear B H2 lookup. inversion H3; subst; simpl in *.
 rewrite H0 in H4. inversion H4. exists super_c. assumption.
 rewrite H1 in H. discriminate.
Save.

Lemma preserve_update : forall classesX classesA classesB preclasses nm pc c,
  preserve_old_classes classesX classesB ->
  preserve_old_classes classesX classesA ->
  only_add_from_preclasses classesX classesB preclasses ->
  only_add_one classesX classesA nm pc ->
  Classpool.lookup (classpool classesA) nm = Some c ->
  (exists pc_c, preclass_to_class pc = Some pc_c
                /\ Classpool.lookup (classpool classesB) nm = Some pc_c) ->
     preserve_old_classes classesA classesB
  /\ only_add_from_preclasses classesA classesB preclasses.
intros classesX classesA classesB preclasses nm pc c.
unfold preserve_old_classes. unfold only_add_from_preclasses. unfold only_add_one. unfold class_loaded.
intros (*not_in_X*) p_X_B p_X_A oa_XB_p oao_XA_nm_pc A_pc pc_c.
assert (preserve_old_classes classesA classesB).
 unfold preserve_old_classes. unfold class_loaded. intros.
 destruct (B.Classname.eq_dec nm nm0) as [nm_eq_nm0 | nm_neq_nm0].
  (* nm = nm0 *)
  subst. destruct (oao_XA_nm_pc _ _ H) as [[nm0_eq pc2c] | [nm0_neq nm_in_X]].
   destruct pc_c as [pc_c [pc_pcc B_nm0_pcc]]. rewrite pc_pcc in pc2c. inversion pc2c. assumption.
   auto.
  (* nm <> nm0 *)
  destruct (oao_XA_nm_pc _ _ H) as [[nm0_eq pc2c] | nm_in_X]; subst; intuition.
split.
 apply H.
 (* only_add_from_preclasses *)
 intros.
 destruct (oa_XB_p _ _ H0) as [from_preclasses | in_X]; intuition.
  destruct (B.Classname.eq_dec nm nm0) as [nm_eq_nm0 | nm_neq_nm0].
   subst. rewrite (H _ _ A_pc) in H0. inversion H0. subst. right. assumption.
   left. destruct from_preclasses as [pc' [pc'2c [lookup_pc' no_X_c']]].
    exists pc'; intuition. destruct (oao_XA_nm_pc _ _ H1).
     destruct H2. symmetry in H2. contradiction.
     destruct H2. eapply no_X_c'. eassumption.
Save.

Lemma preserve_updates : forall classesX classesY classesA classesB preclasses x c1 c2,
 preserve_old_classes classesX classesY ->
 preserve_old_classes classesY classesB ->
 preserve_old_classes classesX classesA ->
 only_add_from_preclasses classesX classesY preclasses ->
 only_add_one classesX classesA (C.preclass_name x) x ->
 only_add_one classesY classesB (C.preclass_name x) x ->
 Classpool.lookup (classpool classesB) (C.preclass_name x) = Some c1 ->
 Classpool.lookup (classpool classesA) (C.preclass_name x) = Some c2 ->
 Preclasspool.lookup preclasses (C.preclass_name x) = Some x ->
    preserve_old_classes classesA classesB
 /\ only_add_from_preclasses classesA classesB preclasses.
intros classesX classesY classesA classesB preclasses x c1 c2.
unfold preserve_old_classes. unfold only_add_from_preclasses. unfold only_add_one. unfold class_loaded.
intros X_in_Y Y_in_B X_in_A oa_XY_p oao_XA_x oao_YB_x x_in_B x_in_A preclasspool_lookup.
assert (preserve_old_classes classesA classesB).
 unfold preserve_old_classes. unfold class_loaded. intros.
 destruct (oao_XA_x _ _ H) as [[H0 H1] | [H0 H1]].
  destruct (oao_YB_x _ _ x_in_B) as [[_ H2] | [H2 _]].
   rewrite <- H1 in H2. inversion H2. subst. assumption.
   intuition.
  auto.

split.
 apply H.
 (* only_add_from_preclasses *)
 intros.
 destruct (oao_YB_x _ _ H0) as [[H1 H2] | [H1 H2]].
  subst. rewrite (H _ _ x_in_A) in H0. inversion H0. subst. right. assumption.
  destruct (oa_XY_p _ _ H2) as [from_preclasses | from_X]; intuition.
   destruct from_preclasses as [pc [pc2c [lookup_pc notin_X]]].
   left. exists pc. intuition. eapply notin_X. destruct (oao_XA_x _ _ H3).
    destruct H4; contradiction.
    destruct H4. eassumption.
Save.

Lemma update_preserve : forall classesA classesB c nm H H2,
  Classpool.lookup (classpool classesA) nm = None ->
  preserve_old_classes classesA classesB ->
  preserve_old_classes classesA (mk_classpool (Classpool.update (classpool classesB) nm c) H H2).
unfold preserve_old_classes. unfold class_loaded. simpl. intros. 
pose (H1 _ _ H3).
destruct (B.Classname.eq_dec nm nm0). 
 subst. rewrite H3 in H0. discriminate.
 rewrite Classpool.indep_lookup; assumption.
Save.

Lemma preserve_not_there : forall a classesA classesB preclasses,
  Classpool.lookup (classpool classesA) a = None ->
  only_add_from_preclasses classesA classesB (Preclasspool.remove a preclasses) ->
  Classpool.lookup (classpool classesB) a = None.
intros. unfold only_add_from_preclasses in *. unfold class_loaded in *. simpl in *.
destruct (Classpool.lookup_informative (classpool classesB) a).
 destruct s. destruct (H0 _ _ e).
  destruct H1. destruct H1. destruct H2.  rewrite Preclasspool.remove_lookup in H2. discriminate.
  rewrite H in H1. discriminate.
 assumption.
Save.

Lemma load_and_resolve_aux_null :
  forall preclasses preclasses' P a classesA classesA' classesB (p:preserve_old_classes classesA classesA') o c c_exists,
  load_and_resolve_aux a preclasses P classesA = load_ok _ p o c c_exists ->
  preserve_old_classes classesA classesB ->
  preclass_incl preclasses preclasses' ->
  only_add_from_preclasses classesA classesB preclasses' ->
  (exists c', Classpool.lookup (classpool classesB) a = Some c') ->
      preserve_old_classes classesA' classesB
   /\ only_add_from_preclasses classesA' classesB preclasses'.
intros preclasses preclasses' P. elim P using Preclasspool.wf_removals_ind2; simpl; intros.

(* Empty preclasses *)
destruct (Classpool.lookup_informative (classpool classesA) a) as [[c_a a_exists] | no_a].
 (* It was already loaded *)
 inversion H. subst. split; trivial.
 (* It wasn't loaded, but this is impossible *)
 destruct (Preclasspool.lookup_informative m a) as [[pc pc_exists] | no_pc].
  clear H. rewrite e in pc_exists. discriminate.
  discriminate.

(* preclasses contains some stuff *)
destruct (Classpool.lookup_informative (classpool classesA) a) as [[c_a c_a_exists] | no_c_a].
 (* It was already there last time *)
 inversion H0. subst. split; trivial.
 (* It wasn't there last time, so we have to dynamically load it *)
 destruct (Preclasspool.lookup_informative s a) as [[pc pc_exists] | no_pc].
  (* It was in the preclasses *)
  destruct (B.Classname.eq_dec (C.preclass_name pc) B.java_lang_Object); try discriminate.
  destruct (B.Classname.eq_dec a (C.preclass_name pc)). 
   (* the names match *)
   destruct (loader_dec (P:=fun classes t => good_interface_list (classpool classes) (C.preclass_super_interfaces pc))
      (load_interfaces (Preclasspool.remove (C.preclass_name pc) s)
         (fun target : B.Classname.t =>
          load_and_resolve_aux target
            (Preclasspool.remove (C.preclass_name pc) s)
            (w (C.preclass_name pc) pc (switch_prenames (sym_eq e) pc_exists)))
         (C.preclass_super_interfaces pc) classesA));
     destruct H5; destruct H5; destruct H5; destruct H5.
    (* loading the interfaces succeeded *)
    destruct H5; rewrite H5 in H0. destruct x2.

    (* Prove some intermediate results *)
    assert (exists pc_c, preclass_to_class pc = Some pc_c /\ Classpool.lookup (classpool classesB) a = Some pc_c).
     destruct H4. destruct (H3 _ _ H4).
      (* a was loaded from preclasses *)
      destruct H6 as [pc' [pc'_is_x2 [preclasses'_a_pc' _]]].
      rewrite (H2 _ _ pc_exists) in preclasses'_a_pc'.
      inversion preclasses'_a_pc'. rewrite pc'_is_x2. exists x2. auto.
      (* a already existed *)
      unfold class_loaded in H6. simpl in H6. rewrite no_c_a in H6. discriminate.
    assert (preserve_old_classes x classesB /\ only_add_from_preclasses x classesB preclasses').
     eapply (load_interfaces_null (C.preclass_super_interfaces pc)
                                  (Preclasspool.remove (C.preclass_name pc) s)
                                  preclasses'
                                  (fun target : B.Classname.t =>
                                    load_and_resolve_aux target
                                      (Preclasspool.remove (C.preclass_name pc) s)
                                      (w (C.preclass_name pc) pc
                                    (switch_prenames (classes:=s) (sym_eq e) pc_exists))) classesA); auto.
      apply H5.
      eapply preclass_incl_trans. apply preclass_incl_remove. apply H2.
      intros. apply (H (C.preclass_name pc) pc (switch_prenames (sym_eq e) pc_exists) a0 classesA0 classesA'0 classesB0 p0 o0 c0 c_ex); auto.
      apply (class_exists_implies_interfaces_exist classesB a); assumption.
    destruct H7.

    (* Now carry on *)
    destruct (bool_informative (C.preclass_interface pc)).
     (* it was an interface *)
     destruct (option_eq_dec B.Classname.eq_dec (C.preclass_super_name pc) (Some B.java_lang_Object)).
      (* It had the correct super class *)
      destruct (add_interface n (only_add_from_preclasses_implies_not_already_there x1 (switch_names (sym_eq e) no_c_a)) x3 e0 e1)
       as [[classes'' c' [preserved' [only_add_one' c'_exists]]] | ex].
       (* adding the interface succeeded *)
       inversion H0. subst classes''. subst c'. rewrite e in H6.
       eapply preserve_update; eassumption.
       (* adding the interface failed *)
       discriminate.
      (* Did not have the correct super class *)
      discriminate.
     (* it wasn't an interface *)
     destruct (option_informative (C.preclass_super_name pc)).
      (* Had a super class *)
      destruct s0. 
      destruct (loader_dec (P:=fun classes c => Classpool.lookup (classpool classes) x2 = Some c)
                 (load_and_resolve_aux x2
                    (Preclasspool.remove (C.preclass_name pc) s)
                    (w (C.preclass_name pc) pc (switch_prenames (sym_eq e) pc_exists)) x));
        destruct H9; destruct H9; destruct H9; destruct H9.
       (* Loading the super class succeeded *)
       destruct H9; rewrite H9 in H0.

       (* apply the induction hypothesis here *)
       assert (preserve_old_classes x4 classesB /\ only_add_from_preclasses x4 classesB preclasses').
        eapply (H (C.preclass_name pc) pc (switch_prenames (sym_eq e) pc_exists) x2 x x4 classesB x5 x6 x7 x8); auto.
         eapply preclass_incl_trans. apply preclass_incl_remove. apply H2.
         eapply class_exists_implies_super_class_exists. apply H6. apply e1. apply e0. 
       destruct H10.

       destruct (bool_informative (C.class_interface x7)).
        (* super class was an interface *)
        discriminate.
        (* super class was really a class *)
        match goal with [H0:match ?x with inl _ => _ | inr _ => _ end = _ |- _] =>
           destruct x as [[classes'' c' [preserved' [only_add_one' c'_exists]]] | ex] end.
         (* adding the class succeeded *)
         inversion H0. subst classes'' c'. rewrite e in H6.
         eapply preserve_update; eauto.
         (* adding the class failed *)
         discriminate.
       (* Loading the super class failed *)
       rewrite H9 in H0. discriminate.
      (* Had no super class *)
      discriminate.
    (* loading the interfaces failed *)
    rewrite H5 in H0. discriminate.
   (* names do not match *)
   discriminate.
  (* wasn't in preclasses *)
  discriminate.
Save.

Lemma preserve_load_interfaces :
  forall l preclasses preclasses' load_and_resolve_aux_rec classes classes' classes1 (preserved1 : preserve_old_classes classes classes1) only_add1 gil1,
  load_interfaces preclasses load_and_resolve_aux_rec l classes = load_ok _ preserved1 only_add1 tt gil1 ->
  preserve_old_classes classes classes' ->
  preclass_incl preclasses preclasses' ->
  only_add_from_preclasses classes classes' preclasses' ->
  (forall nm classesA classesB classesA' (preservedA:preserve_old_classes classesA classesA') only_addA c c_existsA,
    load_and_resolve_aux_rec nm classesA = load_ok _ preservedA only_addA c c_existsA ->
    preserve_old_classes classesA classesB ->
    preclass_incl preclasses preclasses' ->
    only_add_from_preclasses classesA classesB preclasses' ->
    exists classesB', exists preservedB:preserve_old_classes classesB classesB', exists only_addB, exists c_existsB,
     load_and_resolve_aux_rec nm classesB = load_ok _ preservedB only_addB c c_existsB
     /\ preserve_old_classes classesA' classesB'
     /\ only_add_from_preclasses classesA' classesB' preclasses') ->
  exists classes2, exists preserved2 : preserve_old_classes classes' classes2, exists only_add2, exists gil2,
  load_interfaces preclasses load_and_resolve_aux_rec l classes' = load_ok _ preserved2 only_add2 tt gil2
  /\ preserve_old_classes classes1 classes2 /\ only_add_from_preclasses classes1 classes2 preclasses'.
intro l. induction l; intros; simpl in * |- *.

(* empty list *)
exists classes'. exists (preserve_id classes'). exists (only_add_id classes' preclasses). exists (gil_nil (classpool classes')).
 split. 
  reflexivity.
  inversion H. subst. split; trivial.

(* step case *)
destruct (loader_dec (P:=fun classes c => Classpool.lookup (classpool classes) a = Some c)
           (load_and_resolve_aux_rec a classes));
  destruct H4; destruct H4; destruct H4; destruct H4.
 (* loading succeeded *)
 destruct H4. rewrite H4 in H.
 destruct (sumbool_dec (bool_informative (C.class_interface x2))); destruct H5; rewrite H5 in H.
  (* it was an interface *)
  destruct (loader_dec (P:=fun classes t => good_interface_list (classpool classes) l)
             (load_interfaces preclasses load_and_resolve_aux_rec l x));
     destruct H6; destruct H6; destruct H6; destruct H6.
   (* loading the rest succeeded *)
   destruct H6. rewrite H6 in H. destruct x8. 
   destruct (H3 _ _ _ _ _ _ _ _ H4 H0 H1 H2); destruct H7; destruct H7; destruct H7; destruct H7; destruct H8.
   rewrite H7. rewrite H5. 
   destruct (IHl _ _ _ _ _ _ _ _ _ H6 H8 H1 H9 H3); destruct H10; destruct H10; destruct H10; destruct H10; destruct H11.
   rewrite H10. 
   exists x13. exists (compose_preserved x10 x14). exists (compose_only_add x10 x11 x15). 
   exists (gil_cons (i_nm:=a) (rest:=l) (x14 a x2 x12) x4 (cert_classpool_gives_gil (classes:=x13) (nm:=a) (x14 a x2 x12)) x16). 
   split.
    reflexivity.
    inversion H. subst. split; trivial.
   (* loading the rest failed *)
   rewrite H6 in H. discriminate.
  (* it wasn't an interface *)
  discriminate.
 (* loading failed *)
 rewrite H4 in H. discriminate.
Save.

Lemma preclass_to_class_result : forall classesX classesY nm pc c,
  only_add_one classesX classesY nm pc ->
  Classpool.lookup (classpool classesY) nm = Some c ->
  preclass_to_class pc = Some c.
unfold only_add_one.
intros classesX classesY nm pc c oao_XY_nm_pc Y_nm_c.
destruct (oao_XY_nm_pc _ _ Y_nm_c) as [[_ H] | [H _]].
 symmetry. assumption.
 elimtype False. apply H. reflexivity.
Save.
Implicit Arguments preclass_to_class_result [classesX classesY nm pc c].

Lemma add_interface_suceeds : forall classesZ x not_Object not_there gil is_interface super_is_Object c,
 preclass_to_class x = Some c ->
 let P := fun classes' c => preserve_old_classes classesZ classes' /\ only_add_one classesZ classes' (C.preclass_name x) x /\ Classpool.lookup (classpool classes') (C.preclass_name x) = Some c in
 exists classesZ',
 exists p_ZZ' : preserve_old_classes classesZ classesZ',
 exists oao_ZZ' : only_add_one classesZ classesZ' (C.preclass_name x) x,
 exists lookup : Classpool.lookup (classpool classesZ') (C.preclass_name x) = Some c,
   add_interface not_Object not_there gil is_interface super_is_Object =
    inl _ (pack2 P classesZ' c (conj p_ZZ' (conj oao_ZZ' lookup))).
intros classesZ x not_Object not_there gil is_interface super_is_Object c x2c P.
unfold add_interface.
destruct (option_informative (preclass_to_class x)) as [[c' x2c'] | no_c'].
 rewrite x2c' in x2c. inversion x2c. subst.
 match goal with [ |- ex (fun _ => ex (fun _ => ex (fun _ => ex (fun _ => inl exn (pack2 _ ?a ?b (conj ?c (conj ?d ?e))) = _)))) ] =>
  exists a; exists c; exists d; exists e; reflexivity
 end.
 rewrite x2c in no_c'. discriminate.
Save.

Lemma add_class_suceeds : forall classesZ x not_Object not_there gil is_class has_super gsc c,
 preclass_to_class x = Some c ->
 let P := fun classes' c => preserve_old_classes classesZ classes' /\ only_add_one classesZ classes' (C.preclass_name x) x /\ Classpool.lookup (classpool classes') (C.preclass_name x) = Some c in
 exists classesZ',
 exists p_ZZ' : preserve_old_classes classesZ classesZ',
 exists oao_ZZ' : only_add_one classesZ classesZ' (C.preclass_name x) x,
 exists lookup : Classpool.lookup (classpool classesZ') (C.preclass_name x) = Some c,
   add_class not_Object not_there gil is_class has_super gsc =
    inl _ (pack2 P classesZ' c (conj p_ZZ' (conj oao_ZZ' lookup))).
intros classesZ x not_Object not_there gil is_class has_super gsc c x2c P.
unfold add_class.
destruct (option_informative (preclass_to_class x)) as [[c' x2c'] | no_c'].
 rewrite x2c' in x2c. inversion x2c. subst.
 match goal with [ |- ex (fun _ => ex (fun _ => ex (fun _ => ex (fun _ => inl exn (pack2 _ ?a ?b (conj ?c (conj ?d ?e))) = _)))) ] =>
  exists a; exists c; exists d; exists e; reflexivity
 end.
 rewrite x2c in no_c'. discriminate.
Save.

Lemma preserve_load_and_resolve_aux :
  forall preclasses P preclasses' target classes classes' classes1 (preserved1:preserve_old_classes classes classes1) only_add1 c c_exists1,
  load_and_resolve_aux target preclasses P classes = load_ok _ preserved1 only_add1 c c_exists1 ->
  preserve_old_classes classes classes' ->
  only_add_from_preclasses classes classes' preclasses' ->
  preclass_incl preclasses preclasses' ->
  exists classes2, exists preserved2 : preserve_old_classes classes' classes2, exists only_add2, exists c_exists2,
    load_and_resolve_aux target preclasses P classes' = load_ok _ preserved2 only_add2 c c_exists2
    /\ preserve_old_classes classes1 classes2 /\ only_add_from_preclasses classes1 classes2 preclasses'.
intros preclasses P. elim P using Preclasspool.wf_removals_ind2; simpl.

(* empty preclasspool *)
intros emp_preclasses emp_preclasses_is_emp preclasses' target classes classes' classes1 preserved1 only_add1 c c_exists CODE preserved' only_add' incl. 
destruct (Classpool.lookup_informative (classpool classes) target).
 (* It was already in the previous classes *)
 destruct s. inversion CODE. subst. pose (e0:=preserved' _ _ e). unfold class_loaded in *. simpl in *.
 destruct (Classpool.lookup_informative (classpool classes') target). 
  (* this time, it is also already loaded *)
  destruct s. rewrite e1 in e0. inversion e0. subst.
  exists classes'.
  exists (preserve_id classes').
  exists (only_add_id classes' emp_preclasses). 
  exists e1. split.
   reflexivity.
   split; trivial.
  (* this time, it is not already loaded, but this is impossible *)
  elimtype False. rewrite e0 in e1. discriminate.
 (* not in classes: impossible case, since preclasses is empty *)
 elimtype False. destruct (Preclasspool.lookup_informative emp_preclasses target) as [[pc pc_exists] | no_pc].
  clear CODE. rewrite emp_preclasses_is_emp in pc_exists. discriminate.
  discriminate.

(* preclasspool contains something, so we may have to do dynamic loading *)
intros.
destruct (Classpool.lookup_informative (classpool classes) target).
 (* Previously we didn't have to dynamically load it *)
 destruct s0. inversion H0. subst. clear H0.
 pose (e0:=H1 _ _ e). unfold class_loaded in *. simpl in *.
 destruct (Classpool.lookup_informative (classpool classes') target).
  destruct s0. rewrite e1 in e0. inversion e0. subst.
  exists classes'.
  exists (preserve_id classes').
  exists (only_add_id classes' s).
  exists e1. split.
   reflexivity.
   split; trivial.
  (* dynamic loading fails this time round. This is impossible *)
  elimtype False. rewrite e0 in e1. discriminate.
 (* Previously, we had to dynamically load it *)
 destruct (sumor_dec (Preclasspool.lookup_informative s target)); destruct H4.
  (* The target was originally found in the preclasspool *)
  destruct x. rewrite H4 in H0. rewrite H4.
  destruct (B.Classname.eq_dec (C.preclass_name x) B.java_lang_Object) as [X1 | X1]; try discriminate.
  destruct (sumbool_dec (B.Classname.eq_dec target (C.preclass_name x))); destruct H5.
   (* The names are equal *)
   clear H5. subst target. 
   destruct (eq_dec_eq _ B.Classname.eq_dec _ _ (refl_equal (C.preclass_name x))).
   rewrite H5 in H0. rewrite H5.
   (* First we prove something about the recursive calls *)
   set (preclasses0':=Preclasspool.remove (C.preclass_name x) s) in *.
   set (P':=w (C.preclass_name x) x (switch_prenames (sym_eq x0) e0)) in *.
   destruct (loader_dec (P:=fun classes t => good_interface_list (classpool classes) (C.preclass_super_interfaces x))
                   (load_interfaces preclasses0'
                        (fun target0 => load_and_resolve_aux target0 preclasses0' P') (C.preclass_super_interfaces x) classes));
       destruct H6; destruct H6; destruct H6; destruct H6.
    (* loading the interfaces suceeded *)
    destruct H6. rewrite H6 in H0. destruct x4.

    assert (exists classes2, exists preserved2 : preserve_old_classes classes' classes2, exists only_add2, exists gil2,
             load_interfaces preclasses0' (fun x => load_and_resolve_aux x preclasses0' P') (C.preclass_super_interfaces x) classes' = load_ok _ preserved2 only_add2 tt gil2
             /\ preserve_old_classes x1 classes2 /\ only_add_from_preclasses x1 classes2 preclasses').
     apply (preserve_load_interfaces (C.preclass_super_interfaces x) preclasses0' preclasses' 
              (fun x => load_and_resolve_aux x preclasses0' P')
              classes classes' x1 x2 x3 x5 H6); try assumption.
      eapply preclass_incl_trans. unfold preclasses0'. apply preclass_incl_remove. assumption.
      intros. apply (H (C.preclass_name x) x (switch_prenames (sym_eq x0) e0) preclasses' nm classesA classesB classesA' preservedA only_addA c0 c_existsA H7); auto.
    destruct H7; destruct H7; destruct H7; destruct H7. destruct H7. destruct H8.

    destruct (sumbool_dec (bool_informative (C.preclass_interface x))); destruct H10; rewrite H10 in H0; rewrite H10.
     (* this class was an interface *)
     destruct (sumbool_dec (option_eq_dec B.Classname.eq_dec (C.preclass_super_name x) (Some B.java_lang_Object))); destruct H11; rewrite H11 in H0; rewrite H11.
      (* Its super class was java.lang.Object, so we went on to add it *)
      match goal with [_:match ?x with inl _ => _ | inr _ => _ end = _ |- _] =>
        destruct x as [[classes'' c' [preserved' [only_add_one' c'_exists]]] | ex]
      end.
       (* adding the interface succeeded *)
       inversion H0. subst classes'' c'.
       destruct (Classpool.lookup_informative (classpool classes') (C.preclass_name x)) as [[c_x x_exists] | no_x].
        (* lookup in the classpool succeeds this time, meaning we have loaded it from the preclasspool in between *)
        destruct (H2 _ _ x_exists) as [[pc [pc2x [pc_in_preclasses _]]] | x_in_classes].
         (* only_add claims it was dynamically loaded in between, as we thought *)
         rewrite (H3 _ _ e0) in pc_in_preclasses. inversion pc_in_preclasses. subst pc.
         generalize pc2x. intro.
         rewrite (preclass_to_class_result only_add_one' c'_exists) in pc2x. inversion pc2x.   
         generalize x_exists. rewrite <- H13. intro. 
         exists classes'. exists (preserve_id classes'). exists (only_add_id classes' s). exists x_exists0.
         split.
          reflexivity.
          assert (preserve_old_classes x1 classes' /\ only_add_from_preclasses x1 classes' preclasses').
           apply (load_interfaces_null (C.preclass_super_interfaces x)
                                       preclasses0' preclasses'
                                       (fun x : B.Classname.t => load_and_resolve_aux x preclasses0' P')
                                       classes x1 classes' x2 x3 x5); auto. 
            eapply preclass_incl_trans. unfold preclasses0'. apply preclass_incl_remove. assumption.
            intros. apply (load_and_resolve_aux_null preclasses0' preclasses' P' a classesA classesA' classesB p o c0 c_ex H12 H14 H15 H16 H17).
            eapply class_exists_implies_interfaces_exist. exists c_x. split; eassumption.
          destruct H12.
          eapply preserve_update; eauto.
         (* only_add claims it was in classes, but this is a lie *)
         unfold class_loaded in x_in_classes. simpl in x_in_classes. rewrite e in x_in_classes. discriminate.
        (* lookup in the classpool fails from classes', so we must dynamically load it *)
        rewrite H7.
        destruct (add_interface_suceeds x4 x X1 (only_add_from_preclasses_implies_not_already_there x7 (switch_names (sym_eq x0) no_x)) x8 x9 x10 c)
              as [classes'' [p'' [oao'' [lookup'' add_interface_eq]]]].
         eapply preclass_to_class_result; eassumption.
        rewrite add_interface_eq.
        eapply ex_intro. eapply ex_intro. eapply ex_intro. eapply ex_intro. split.
         reflexivity.
         eapply preserve_updates.
          apply H8.
          assumption.
          assumption.
          assumption.
          apply only_add_one'.
          apply oao''.
          eassumption.
          eassumption.
          apply (H3 _ _ e0).
       (* adding this interface failed *)
       discriminate.
      (* Its super class was something else, so we returned an error *)
      discriminate.
     (* it was a proper class *)
     destruct (option_informative (C.preclass_super_name x)).
      (* it has a super class *)
      destruct s0.
      destruct (loader_dec (P:=fun classes c => Classpool.lookup (classpool classes) x10 = Some c)
                 (load_and_resolve_aux x10 preclasses0' P' x1));
         destruct H11; destruct H11; destruct H11; destruct H11.
       (* loading the super class suceeded *)
       destruct H11. rewrite H11 in H0.
       destruct (bool_informative (C.class_interface x14)).
        (* the super class turned out to be an interface *)
        discriminate.
        (* the super class really was a class *)
        match goal with [_:match ?x with inl _ => _ | inr _ => _ end = _ |- _] =>
         destruct x as [[classes'' c' [preserved' [only_add_one' c'_exists]]] | ex]
        end.
         (* adding the class originally suceeded FIXME HERE*)
         inversion H0. subst classes'' c'. clear H0.
         destruct (Classpool.lookup_informative (classpool classes') (C.preclass_name x)) as [[c_x x_exists] | no_x].
          (* lookup in classes' succeeds, meaning it has been loaded in between classes and classes' *)
          destruct (H2 _ _ x_exists) as [[pc [pc2c_x [pc_exists _]]] | c_x_loaded].
           (* only_add claims it was dyamically loaded in between, as we thought *)
           rewrite (H3 _ _ e0) in pc_exists. inversion pc_exists. subst pc. clear pc_exists.
           generalize pc2c_x. intro.
           rewrite (preclass_to_class_result only_add_one' c'_exists) in pc2c_x. inversion pc2c_x.   
           generalize x_exists. rewrite <- H12. intro.
           eapply ex_intro. eapply ex_intro. eapply ex_intro. eapply ex_intro. split.
            reflexivity.
            assert (preserve_old_classes x1 classes' /\ only_add_from_preclasses x1 classes' preclasses').
             apply (load_interfaces_null (C.preclass_super_interfaces x)
                                         preclasses0' preclasses'
                                         (fun x : B.Classname.t => load_and_resolve_aux x preclasses0' P')
                                         classes x1 classes' x2 x3 x5); auto. 
              eapply preclass_incl_trans. unfold preclasses0'. apply preclass_incl_remove. assumption.
              intros. apply (load_and_resolve_aux_null preclasses0' preclasses' P' a classesA classesA' classesB p o c0 c_ex H0 H13 H14 H15 H16).
              eapply class_exists_implies_interfaces_exist. exists c_x; eauto.
            destruct H0.
            assert (preserve_old_classes x11 classes' /\ only_add_from_preclasses x11 classes' preclasses').
             apply (load_and_resolve_aux_null preclasses0' preclasses' P' x10 x1 x11 classes' x12 x13 x14 x15 H11); auto.
              eapply preclass_incl_trans. unfold preclasses0'. apply preclass_incl_remove. assumption.
              eapply class_exists_implies_super_class_exists. exists c_x; eauto. assumption. assumption.
            destruct H14.
            eapply preserve_update; eauto.
           (* only_add claims it was in classes, but this is a lie *)
           unfold class_loaded in c_x_loaded. simpl in c_x_loaded. rewrite e in c_x_loaded. discriminate.
          (* lookup in classes' fails, so we dynamically load it again *)
          rewrite H7.

          destruct (H (C.preclass_name x) x (switch_prenames (sym_eq x0) e0) preclasses' x10 x1 x4 x11 x12 x13 x14 x15 H11 H8 H9)
                as [classes'' [preserved'' [only_add'' [super_c_exists [lara_res [preserved''' only_add''']]]]]].
           eapply preclass_incl_trans. apply preclass_incl_remove. assumption.
          unfold preclasses0'. unfold P'. rewrite lara_res. 
          destruct (bool_informative (C.class_interface x14)) as [x14_interface | x14_class]. 
           (* This time it is really an interface!, but this is a lie *)
           elimtype False. rewrite e2 in x14_interface. discriminate.
           (* Phew, the super class is a class *)
           match goal with [|- ex (fun _ => ex (fun _ => ex (fun _ => ex (fun _ => 
                                   match add_class ?A ?B ?C ?D ?E ?F with inl _ => _ | inr _ => _ end = _ /\ _))))] => 
             destruct (add_class_suceeds classes'' x A B C D E F c)
                   as [classes''' [p''' [oao''' [lookup''' add_interface_eq]]]]
           end.
            eapply preclass_to_class_result; eassumption.
           rewrite add_interface_eq.
           eapply ex_intro. eapply ex_intro. eapply ex_intro. eapply ex_intro. split.
             reflexivity.
             eapply preserve_updates.
              apply preserved'''.
              assumption.
              assumption.
              assumption.
              apply only_add_one'.
              apply oao'''.
              eassumption.
              eassumption.
              apply (H3 _ _ e0).
         (* adding the class originally failed *)
         discriminate.
       (* loading the super class failed *)
       rewrite H11 in H0. discriminate.
      (* it had no super class, so we went on to add it *)
      discriminate.
    (* loading the interfaces failed *)
    rewrite H6 in H0. discriminate.
   (* The names are not equal *)
   rewrite H5 in H0. discriminate. 
  (* The target was not found in the preclasspool *)
  rewrite H4 in H0. discriminate.
Save.

(* FIXME: this is a hack: *)
Definition gather_class_exists_evidence : forall classes nm,
  unit+{exists c, class_loaded classes nm c /\ C.class_interface c = false}.
intros.
destruct (Classpool.lookup_informative (classpool classes) nm) as [[c c_exists] | no_c].
 (* nm exists *)
 destruct (bool_informative (C.class_interface c)) as [is_interface | is_class].
  (* is interface *)
  left. constructor.
  (* is class *)
  right. exists c. auto.
 (* nm doesn't exist *)
 left. constructor.
Defined.


End MkClasspool.

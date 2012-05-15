Require Import ClassDatatypesIface.
Require Import ILL.ILLInterfaces.
Require Import BasicMachineTypes.
Require Import OptionExt.
Require Import ListExt.
Require Import ClasspoolIface.
Require Import CertRuntimeTypesIface.
Require Import List.
Require Import JVMState.
Require Import SafeNativeMethods.
Require Execution.
Require Import Certificates.
Require Import StoreIface.
Require Import ResourceAlgebra.
Require Import AssignabilityIface.
Require Import PreassignabilityIface.
Require Import VirtualMethodLookupIface.
Require Import ResolutionIface.
Require Import VerifierAnnotationsIface.
Require Import Setoid.
Require BuiltinClasses.

Require Import AbstractLogic.
Require Import NativeMethodSpec.
Require Import ResourceLogicIface.

Module ResourceSafety
  (B    : BASICS)
  (BASESEM : ILL_BASE_SEMANTICS B)
  (SYN  : ILL_SYNTAX B BASESEM.SYN)
  (CERT : CERTIFICATE         with Definition asn := BASESEM.SYN.formula)
  (AL   : ILL_TYPE B BASESEM.SYN SYN)
  (ANN  : VERIFIER_ANNOTATIONS B AL CERT)
  (C    : CLASSDATATYPES B ANN.GA.A)
  (CP   : CLASSPOOL B ANN.GA.A C)
  (A    : ASSIGNABILITY B ANN.GA.A C  CP)
  (R    : RESOLUTION B ANN.GA.A C CP A)
  (RT   : CERTRUNTIMETYPES B ANN.GA.A C CP A)
  (RSEM : ILL_SEMANTICS B BASESEM SYN)
  (VM   : VIRTUALMETHODLOOKUP B ANN.GA.A C CP A)
  (PA   : PREASSIGNABILITY B ANN.GA C CP A VM)
  (CLSNM: FSetInterface.S     with Definition E.t := B.Classname.t with Definition E.eq := B.Classname.eq)
  (NTSPC: NATIVE_METHOD_SPEC B ANN.GA.A)
  (RL   : RESOURCE_LOGIC B BASESEM SYN CERT AL ANN C CP A R RT RSEM VM PA CLSNM NTSPC)
  (JVM  : JVMSTATE B BASESEM.RA ANN.GA.A C CP A R VM RT)
  (SNM  : SAFE_NATIVE_METHODS B BASESEM SYN CERT AL ANN C CP A R RT RSEM VM PA CLSNM NTSPC RL JVM).

Import SYN.
Import RSEM.
Import BASESEM.SYN.
Import BASESEM.
Import RA.
Import CERT.

Module E := Execution.Execution B RA ANN.GA.A C CP A R VM RT JVM SNM.NM CLSNM.

Import RL.

Module DUMMY.
End DUMMY.

Section WithPreclasses.

Hypothesis preclasses : CP.Preclasspool.t.
Hypothesis privclasses : CLSNM.t.

(** ** Safe results
    The result of executing a step of the machine is safe if
      - it is another safe state,
      - the machine has stopped normally,
      - the machine has stopped due to an uncaught exception, or
      - the machine is in a state ruled out by the JVM's built in verification.

    Additionally, changes to the resource limit may only occur in priviledged
    classes.
  *)

Definition safe_result s result :=
   (exists s', JVM.cont s' = result /\ safe_state preclasses privclasses s' /\ safe_allowance_change privclasses s s')
 \/(exists s', exists v, JVM.stop s' v = result /\ safe_allowance_change privclasses s s' /\ RT.state_res res s' <: RT.state_reslimit res s')
 \/(exists s', exists e, JVM.stop_exn s' e = result /\ safe_allowance_change privclasses s s' /\ RT.state_res res s' <: RT.state_reslimit res s')
 \/(JVM.wrong = result).

(** ** Virtual method lookup and specifications.
    Ensure that the method found by runtime virtual method lookup has a
    specification compatible with the method given.
  *)

Lemma virtual_method_lookup_matches_specification :
  forall classes nmA nmB nmC nmD cA cB cD mB mD mdesc,
  (* not doing <init> *)
  fst mdesc <> B.init ->

  (* overrides are correct *)
  all_classes_verified preclasses privclasses classes ->

  (* The resolved method *)
  CP.class_loaded classes nmD cD ->
  C.MethodList.lookup (C.class_methods cD) mdesc = Some mD ->
  C.method_static mD = false ->
  
  (* relationship between C and D *)
  A.assignable classes nmC (C.ty_obj nmD) ->

  (* The runtime method *)
  CP.class_loaded classes nmB cB ->
  C.MethodList.lookup (C.class_methods cB) mdesc = Some mB ->
  C.method_static mB = false ->
  C.class_interface cB = false ->

  (* The runtime class *)
  CP.class_loaded classes nmA cA ->
  C.class_interface cA = false ->

  (* relationship between A and B, A and C *)
  A.assignable classes (C.ty_obj nmA) (C.ty_obj nmB) ->
  A.assignable classes (C.ty_obj nmA) nmC ->

  (* lookup was minimal *)
  VM.lookup_minimal classes nmA nmB mdesc ->

  (* gives: *)
  safe_override (method_spec mB) (method_spec mD).
intros classes nmA nmB nmC nmD cA cB cD mB mD mdesc.
intros not_init overrides_ok D_exists mD_exists mD_instance C_sub_D.
intros B_exists mB_exists mB_instance B_is_class.
intros A_exists A_is_class A_sub_B A_sub_C lookup_min.

(* get that A <: D *)
assert (A_sub_D : A.assignable classes (C.ty_obj nmA) (C.ty_obj nmD)).
 eapply A.assignable_trans; eauto.

destruct (B.Classname.eq_dec nmD nmB) as [D_eq_B|D_neq_B].
 (* B = D *)
 subst.
 assert (cB=cD); [eapply CP.class_loaded_unique; eassumption|]. subst.
 rewrite mB_exists in mD_exists. inversion mD_exists.
 apply safe_override_refl.

 (* B <> D *)
 destruct (BoolExt.bool_informative (C.class_interface cD)) as [D_interface | D_is_class].
  (* D is an interface *)
  rewrite <- (CP.cert_classpool_names_2 A_exists) in A_sub_B, A_sub_D, lookup_min.
  eapply (class_verified_implements_interfaces _ _ _ _ (overrides_ok _ _ A_exists A_is_class) cD _ _ _ _ cB); eauto.
  (* D is a class *)
  destruct (A.assignable_shared_subclass classes nmA nmB nmD cA cB cD) as [B_sub_D | D_sub_B]; try assumption.
   (* B <: D *)
   rewrite <- (CP.cert_classpool_names_2 B_exists) in B_sub_D.
   eapply (class_verified_overrides_classes _ _ _ _ (overrides_ok _ _ B_exists B_is_class) cD); eauto.
   (* D <: B *)
   destruct (lookup_min nmD cD); try assumption.
    rewrite H in mD_exists. discriminate. 
    destruct H as [mD' [mD'_exists mD'_instance]].
     rewrite mD'_exists in mD_exists. inversion mD_exists. subst.
     rewrite mD_instance in mD'_instance. discriminate.
Save.

(** ** Some lemmas about safe states/stacks/etc. *)

Lemma safe_frame_stack_leq : forall classes fs r r',
 safe_frame_stack preclasses privclasses classes fs r ->
 r <: r' ->
 safe_frame_stack preclasses privclasses classes fs r'.
intros classes fs r r' safe_r r_leq_r'.
destruct safe_r.
eapply mk_safe_current_frame; eauto.
 eapply leq_trans; eauto.
Save.

Lemma safe_frame_stack_has_frames : forall classes frames r,
 safe_frame_stack preclasses privclasses classes frames r -> exists f, exists fs, frames = f::fs.
intros. destruct H. eapply ex_intro. eapply ex_intro. reflexivity.
Save.

(** ** Preservation
    Show that loading classes preserves correctness properties. *)

Lemma preserve_constantpool_additional_correct : forall classes classes' caller cp cpa,
 constantpool_additional_correct preclasses classes caller cp cpa ->
 CP.preserve_old_classes classes classes' ->
 CP.only_add_from_preclasses classes classes' preclasses ->
 constantpool_additional_correct preclasses classes' caller cp cpa.
intros. constructor.
 (* class_instantiable *)
 intros. destruct (cpa_ins_class preclasses classes _ _ _ H idx clsnm H2 H3) as [classes'' [p [oa [c [H' [resolve_ok [not_interface not_abstract]]]]]]].
 destruct (R.preserve_resolve_class _ _ _ _ _ _ _ _ _ _ resolve_ok H0 H1)
       as [classes''' [pB [oB [c_exB [resolve_ok2 _]]]]].
 intuition eauto 8.
 (* static_method *)
 intros. destruct (cpa_static_method _ _ _ _ _ H _ _ _ _ _ _ _ H2 H3) as [classes'' [p [oa [c [m [H' [resolve_ok stuff]]]]]]]. 
 destruct (R.preserve_resolve_method _ _ _ _ _ _ _ _ _ _ _ _ resolve_ok H0 H1)
       as [classes''' [pB [oB [HB resolve_ok2]]]].
 intuition eauto 12.
 (* static field *)
 intros. destruct (cpa_static_field _ _ _ _ _ H _ _ _ _ H2 H3) as [classes'' [p [oa [c [f [H' [resolve_ok static]]]]]]].
 destruct (R.preserve_resolve_field _ _ _ _ _ _ _ _ _ _ _ _ resolve_ok H0 H1)
       as [classes''' [pB [oB [HB resolve_ok2]]]].
 intuition eauto 8.
 (* instance field *)
 intros. destruct (cpa_instance_field _ _ _ _ _ H _ _ _ _ H2 H3) as [classes'' [p [oa [c [f [H' [resolve_ok not_static]]]]]]].
 destruct (R.preserve_resolve_field _ _ _ _ _ _ _ _ _ _ _ _ resolve_ok H0 H1)
       as [classes''' [pB [oB [HB resolve_ok2]]]].
 intuition eauto 9.
 (* normal class ref *)
 intros. destruct (cpa_classref _ _ _ _ _ H idx clsnm H2 H3) as [classes'' [p [oa [c [H' resolve_ok]]]]].
 destruct (R.preserve_resolve_class _ _ _ _ _ _ _ _ _ _ resolve_ok H0 H1)
       as [classes''' [pB [oB [c_exB [resolve_ok2 _]]]]].
 intuition eauto 6.
 (* instance special method *)
 intros. destruct (cpa_instance_special_method _ _ _ _ _  H _ _ _ _ _ _ _ H2 H3) as [classes'' [p [oa [c [m [H' [resolve_ok B]]]]]]].
 destruct (R.preserve_resolve_method _ _ _ _ _ _ _ _ _ _ _ _ resolve_ok H0 H1)
       as [classes''' [pB [oB [HB resolve_ok2]]]].
 intuition eauto 13.
 (* instance method *)
 intros. destruct (cpa_instance_method _ _ _ _ _ H _ _ _ _ _ _ _ H2 H3) as [classes'' [p [oa [c [m [H' [resolve_ok B]]]]]]].
 destruct (R.preserve_resolve_method _ _ _ _ _ _ _ _ _ _ _ _ resolve_ok H0 H1)
       as [classes''' [pB [oB [HB resolve_ok2]]]].
 intuition eauto 12.
 (* interface method *)
 intros. destruct (cpa_interface_method _ _ _ _ _ H _ _ _ _ _ _ _ H2 H3) as [classes'' [p [oa [c [m [H' [resolve_ok B]]]]]]].
 destruct (R.preserve_resolve_interface_method _ _ _ _ _ _ _ _ _ _ _ _ resolve_ok H0 H1)
       as [classes''' [pB [oB [HB resolve_ok2]]]].
 intuition eauto 12.
Save.

Lemma preserve_safe_frame_stack_rest : forall classes classes' fs ensures exsures r,
 safe_frame_stack_rest preclasses privclasses classes fs ensures exsures r ->
 CP.preserve_old_classes classes classes' ->
 CP.only_add_from_preclasses classes classes' preclasses ->
 safe_frame_stack_rest preclasses privclasses classes' fs ensures exsures r.
induction fs; intros; inversion H; econstructor; eauto.
 eapply preserve_constantpool_additional_correct; eauto.
Save.

Lemma reflect_not_loaded : forall classes classes' nm,
 (forall c, ~CP.class_loaded classes' nm c) ->
 CP.preserve_old_classes classes classes' ->
 (forall c, ~CP.class_loaded classes nm c).
unfold CP.preserve_old_classes. eauto.
Qed.

Lemma preserve_preclass_verified : forall classes classes' pc,
 preclass_verified preclasses privclasses classes pc ->
 CP.preserve_old_classes classes classes' ->
 CP.only_add_from_preclasses classes classes' preclasses ->
 preclass_verified preclasses privclasses classes' pc.
intros. constructor.
 (* constant pool annotations are still correct *)
 eauto using preclass_verified_cpa_ok, preserve_constantpool_additional_correct.
 (* methods stay verified *)
 eauto using preclass_verified_methods.
 (* methods in super classes that have been loaded are still safely overidden *) 
 intros. destruct (H1 _ _ H4) as [[pc' [pc'_c [nm_pc' not_loaded]]] | nm_c].
  (* super class was not previously loaded *)
  assert (C.preclass_interface pc' = false /\ exists pm, mB = CP.premethod_to_method pm /\ C.has_premethod (C.preclass_methods pc') md pm).
   destruct (CP.preclass_to_class_props _ _ pc'_c) as [_ [_ [X1 [X2 _]]]].
   rewrite X1. rewrite <- X2.
   auto.
  destruct H11 as [pc'_class [pm [mB_pm pc'_has_pm]]].
  replace (method_spec mB) with (premethod_spec pm); [|subst mB; destruct pm; reflexivity].
  replace (C.method_static mB) with (C.premethod_static pm) in H10; [|subst mB; destruct pm; reflexivity].
  eauto using preclass_verified_overrides_classes2, PA.pc_loaded_cross_super_class.
  (* super class was previously loaded *)
  eauto using preclass_verified_overrides_classes1, PA.pc_preserve_cross_sub_class.
 (* methods in super classes not yet loaded are still safely overridden *)
 intros. eapply preclass_verified_overrides_classes2. 
  eassumption.
  eassumption.
  assumption.
  eassumption.
  intro. eapply reflect_not_loaded. eassumption.
  assumption.
  eauto using PA.pc_preserve_sub_class.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
(* interfaces implemented *)
 intros. destruct (preclass_verified_implements _ _ _ _ H iface md ispec) as [mspec [minimal safe]]; eauto using PA.should_implement_preserved_rev.
 eapply (proj2 (PA.interface_reqs_preserved _ _ _ iface md ispec H0 H1)); eauto.
 pose (proj1 (PA.minimal_methodspec_preserved _ _ _ (C.preclass_name pc) md mspec H0 H1)); eauto.
Qed.

Lemma preserve_all_preclasses_verified : forall classes classes',
 all_preclasses_verified preclasses privclasses classes ->
 CP.preserve_old_classes classes classes' ->
 CP.only_add_from_preclasses classes classes' preclasses ->
 all_preclasses_verified preclasses privclasses classes'.
unfold all_preclasses_verified.
intros.
eapply preserve_preclass_verified.
  eapply H.
   apply H2.
   assumption.
   unfold not. intros. refine (H4 _ _). apply H0. eassumption.
  assumption.
  assumption.
Save.

Lemma preserve_verified_code : forall cp cpa Q X pcode cert,
 verified_precode cp cpa Q X pcode cert ->
 verified_code cp cpa Q X (CP.precode_to_code pcode) cert.
intros. destruct H. constructor; auto.
Save.

Lemma preserve_all_classes_verified : forall classes classes',
 all_classes_verified preclasses privclasses classes ->
 CP.preserve_old_classes classes classes' ->
 CP.only_add_from_preclasses classes classes' preclasses ->
 all_preclasses_verified preclasses privclasses classes ->
 all_classes_verified preclasses privclasses classes'.
intros classes classes' all_classes_ok p oa all_pc_classes'.
unfold all_classes_verified. intros cnm class class_loaded not_interface.
destruct (oa _ _ class_loaded) as [[pc [pc2class [cnm_pc not_loaded]]] | already_loaded].
 (* this class was loaded from the preclases *)
 destruct (CP.preclass_to_class_props _ _ pc2class) as [names [cps [methods [interface _]]]].
 destruct (all_pc_classes' _ _ cnm_pc) as [cpa_ok meths_verified override1 override2 implements].
  rewrite interface in not_interface. assumption. assumption.
 econstructor.
  (* constantpool annotations are still correct *)
  rewrite names. rewrite cps. eauto using preserve_constantpool_additional_correct.
  (* methods are all still verified *)
  clear cpa_ok override1 override2.
  intros. rewrite <- methods in H. destruct H as [pm [m_pm has_pm]].
   subst m. destruct pm. simpl in *. destruct (meths_verified md _ has_pm) as [[code code_verified]|[no_code native_ok]]. 
    left. exists (CP.precode_to_code code). intros. destruct (code_verified P Q X H) as [cert [P' [Q' [has_code [grants [v_pc [P_P' cert_P']]]]]]].
     exists cert. exists P'. exists Q'. simpl in has_code. rewrite has_code in *. split.
      reflexivity.
      unfold method_grants_ok in *. simpl in *. rewrite H. rewrite names. simpl in *. rewrite cps. intuition. 
      apply preserve_verified_code; assumption.
      apply preserve_verified_code; assumption.
    right. simpl in *. rewrite no_code, names.  intuition.
  (* class loaded from the preclasses overrides methods correctly *)
  intros. rewrite <- methods in H4. destruct H4 as [pm [mA_pm has_pm]].
  replace (method_spec mA) with (premethod_spec pm).
  destruct (oa _ _ H1) as [[pcB [pcB_cB [nmB_pcB nmB_not_loaded]]] | nmB_loaded].
   (* B wasn't loaded last time *)
   assert (C.preclass_interface pcB = false /\ exists pm, mB = CP.premethod_to_method pm /\ C.has_premethod (C.preclass_methods pcB) md pm).
    destruct (CP.preclass_to_class_props _ _ pcB_cB) as [_ [_ [X1 [X2 _]]]].
    rewrite X1. rewrite <- X2.
    auto.
   destruct H4 as [pcB_class [pmB [mB_pmB pcB_pmB]]].
   replace (method_spec mB) with (premethod_spec pmB).
   eapply override2. 
    eassumption.
    rewrite <- interface. assumption.
    apply nmB_pcB.
    assumption.
    rewrite <- names. rewrite <- (CP.cert_classpool_names_2 class_loaded) in not_loaded.  assert (A.sub_class classes' (C.class_name class) nmB).  apply A.get_sub_class with (cA:=class) (cB:=cB); auto.  rewrite (CP.cert_classpool_names_2 class_loaded). assumption. eapply PA.pc_loaded_sub_class. apply H4. eauto using PA.pc_loaded_sub_class. 
    assumption.
    assumption.
    assumption.
    assumption.
    eassumption.
    eassumption.
    destruct pm; destruct mA; inversion mA_pm; subst premethod_static; assumption.
    destruct pmB; destruct mB; inversion mB_pmB; subst premethod_static; assumption.
   rewrite mB_pmB. destruct pmB; reflexivity.
   (* B was loaded last time *)
   eapply override1.
    eassumption.
    rewrite <- interface. assumption.
    apply nmB_loaded.
    rewrite <- names. rewrite <- (CP.cert_classpool_names_2 class_loaded) in not_loaded. eapply PA.pc_loaded_cross_sub_class. apply A.get_sub_class with (cA:=class) (cB:=cB); auto.  rewrite (CP.cert_classpool_names_2 class_loaded). apply class_loaded. assumption. eassumption.
    assumption.
    eassumption.
    assumption.
    eassumption.
    eassumption.
    destruct pm; destruct mA; inversion mA_pm; subst premethod_static; assumption.
    assumption.
  rewrite mA_pm. destruct pm; reflexivity.
  (* class loaded from preclasses implements interface methods correctly *)
  intros.
   destruct (PA.convert_iface_req classes' preclasses cnm nmI class cI md mI) as [nmI' [should' iface_meth']]; auto.
   rewrite <- (CP.cert_classpool_names_2 class_loaded). assumption.
   destruct (implements nmI' md (method_spec mI)) as [mspec [minimal safe]]; eauto.
    rewrite <- names. rewrite (CP.cert_classpool_names_2 class_loaded).
    eapply PA.should_implement_preserved_rev; eauto.
    apply (proj2 (PA.interface_reqs_preserved _ _ _ nmI' md (method_spec mI) p oa)). auto.
    apply (proj1 (PA.minimal_methodspec_preserved _ _ _ (C.preclass_name pc) md mspec p oa)) in minimal.
    rewrite <- names in minimal. rewrite (CP.cert_classpool_names_2 class_loaded) in minimal.
    inversion minimal.
      destruct (H11 class class_loaded).

      rewrite (CP.cert_classpool_names_2 class_loaded) in H6.
      assert (nmS = nmB).
       destruct (A.assignable_shared_subclass classes' cnm nmB nmS class cB cS); auto. eapply A.assignable_class_class; eauto.
        assert (A.sub_class classes' nmB nmS) by (eapply A.get_sub_class; eauto). inversion H21.
         reflexivity.
         subst.  rewrite (CP.class_loaded_unique H22 H5) in *.  destruct (H14 nmB cB) as [none|[m' [lookup_m' static_m']]]; auto. apply (A.subclass_distinct _ _ _ _ _ H5 H23 H7 H24).
          rewrite H8 in none. discriminate.
          rewrite H8 in lookup_m'. injection lookup_m' as m'eq. subst m'.
          rewrite H9 in static_m'. discriminate.
        assert (A.sub_class classes' nmS nmB) by (eapply A.get_sub_class; eauto). inversion H21.
         reflexivity.
         subst.  rewrite (CP.class_loaded_unique H22 H15) in *. clear H22. rewrite (CP.cert_classpool_names_2 class_loaded) in H10. destruct (H10 nmS cS) as [none|[m' [lookup_m' static_m']]]; auto. eapply A.assignable_class_class; eauto. apply (A.subclass_distinct _ _ _ _ _ H15 H23 H16 H24).
          rewrite H17 in none. discriminate.
          rewrite H17 in lookup_m'. injection lookup_m' as m'eq. subst m'.
          rewrite H19 in static_m'. discriminate.
      subst nmS. rewrite (CP.class_loaded_unique H15 H5) in H17.  rewrite H8 in H17. injection H17 as meq. subst m.
      rewrite <- H18 in safe.
      apply safe.

      destruct (H11 class class_loaded).

 (* this class was already loaded *)
 (* this class was already in classes *)
 destruct (all_classes_ok _ _ already_loaded). assumption. econstructor.
  eapply preserve_constantpool_additional_correct; eassumption.
  assumption.
  intros. rewrite -> (CP.cert_classpool_names_2 class_loaded) in H2. 
  pose (s := A.get_sub_class _ _ _ _ _ class_loaded H1 not_interface H3 H2).
  apply A.preserve_subclass_rev with (classesA:=classes) (c_s:=class) in s.
  destruct (A.superclass_loaded classes cnm class nmB) as [cB' loadedB]; auto.
  rewrite (CP.class_loaded_unique (p _ _ loadedB) H1) in loadedB; auto.
  apply (class_verified_overrides_classes0 cB nmB md mA mB); eauto.
    apply A.assignable_class_class with (cS:=class) (cT:=cB); auto.
    rewrite (CP.cert_classpool_names_2 class_loaded). assumption.
    rewrite (CP.cert_classpool_names_2 class_loaded). assumption.
    assumption.
    assumption.

  intros.
    assert (CP.class_loaded classes (C.class_name class) class). rewrite (CP.cert_classpool_names_2 already_loaded). assumption.
    apply A.preserve_assignable_rev with (classesA:=classes) (cA:=class) in H2; auto.
    apply A.preserve_assignable_rev with (classesA:=classes) (cA:=class) in H6; auto.
    destruct (A.assignable_loaded classes (C.class_name class) class nmI) as [cI' loadedI']; auto.
    destruct (A.assignable_loaded classes (C.class_name class) class nmB) as [cB' loadedB']; auto.
    rewrite (CP.class_loaded_unique (p _ _ loadedI') H1) in loadedI'.
    rewrite (CP.class_loaded_unique (p _ _ loadedB') H5) in loadedB'.
    apply (class_verified_implements_interfaces0 cI nmI md mI nmB cB mB); eauto.
  
    clear cB' loadedB'.
    intros nmB' cB' ass1 ass2 loadedB' classB' B'notB.
    apply (H10 nmB' cB'); eauto.
      eapply A.preserve_assignable; eauto.
      eapply A.preserve_assignable; eauto.
Save.

(** ** Misc lemmas *)

Lemma sat_and_1 : forall r a a', sat r (f_and a a') -> sat r a.
intros. simpl in H. destruct H. assumption. 
Qed.

Lemma sat_and_2 : forall r a a', sat r (f_and a a') -> sat r a'.
intros. simpl in H. destruct H. assumption. 
Qed.

Lemma unchanging_allowance_ok : forall s s0 result,
 (forall s', safe_allowance_change privclasses s s'  -> safe_allowance_change privclasses s0 s') ->
 safe_result s result ->
 safe_result s0 result.
Proof.
 unfold safe_result.
 intros. decompose [or ex and] H0.
 left. exists x. auto using H.
 right. left. exists x. exists x0. auto using H.
 right. right. left. exists x. exists x0. auto using H.
 right. right. right. auto.
Qed.

(** ** Exception handling *)

Lemma search_handlers_prop : forall classes cert exsures handlers a pc class exc_cls,
 exception_handlers_assertion cert exsures pc handlers a ->
   (exists pc', exists a', E.search_handlers classes handlers pc class exc_cls = E.handler_found pc' /\ Cert.lookup cert pc' = Some a' /\ (forall r, sat r a -> sat r a'))
 \/(E.search_handlers classes handlers pc class exc_cls = E.handler_notfound /\ (forall r, sat r a -> sat r exsures))
 \/(E.search_handlers classes handlers pc class exc_cls = E.handler_wrong).
intros classes cert exsures handlers a pc class exc_cls.
intros eha.
set (a2:=a) in eha. assert (forall r, sat r a -> sat r a2) by auto.
generalize a2 a H pc eha. clear a2 a H pc eha.
induction handlers; intros.
 (* nil *)
 inversion eha. simpl. subst. right. left. intuition.
 (* cons *)
 inversion eha; destruct a; inversion H0; simpl; subst. 
  destruct (C.is_within exc_start_pc exc_end_pc pc).
   destruct exc_catch_type. destruct (C.ConstantPool.lookup (C.class_constantpool class) t); try (right; right; subst; reflexivity). 
    destruct o; try (right; right; subst; reflexivity).
     destruct (A.is_assignable classes (C.ty_obj exc_cls) (C.ty_obj t0)).
      left. exists exc_handler_pc. exists a1. intuition eauto using sat_and_1.
      eauto using sat_and_2.
     left. exists exc_handler_pc. exists a1. intuition eauto using sat_and_1.
    elimtype False. omega.
  destruct (C.is_within exc_start_pc exc_end_pc pc).
   elimtype False. omega.
   eauto.
Save.

Lemma unwind_stack_prop : forall classes frames ref exc_cls frames' current_allowance callee_ensures callee_exsures,
 E.unwind_stack classes frames ref exc_cls = Some frames' ->
 safe_frame_stack_rest preclasses privclasses classes frames callee_ensures callee_exsures current_allowance ->
    (forall r, sat r callee_exsures -> safe_frame_stack preclasses privclasses classes frames' (r :*: current_allowance))
 \/ frames' = nil.
intros classes frames ref exc_cls frames' current_allowance callee_ensures callee_exsures unwind_result frames_safe.
generalize callee_ensures callee_exsures current_allowance frames_safe. clear callee_ensures callee_exsures current_allowance frames_safe.
induction frames; intros.
 (* nil *)
 inversion unwind_result. right. reflexivity.
 (* cons *)
 simpl in unwind_result. destruct a.
 inversion frames_safe. subst. clear frames_safe.
 destruct (search_handlers_prop classes _ _ _ _ _ frame_class exc_cls H13)
       as [[pc' [a' [search_result [lookup_res ex_assertion_implies_a]]]]
          | [ [search_result a_implies_exsures]
            | search_result ]]; rewrite search_result in unwind_result.
  (* search found something *)
  left. intros. inversion unwind_result. subst. clear unwind_result IHframes.
  eapply mk_safe_current_frame.
   apply H7.
   apply H8.
   apply lookup_res.
   eauto.
   rewrite <- combine_assoc. rewrite combine_symm. rewrite <- combine_assoc. apply combine_order.
    apply leq_refl. reflexivity.
    rewrite combine_symm. apply H16.
   eassumption.
   reflexivity.
   apply H6.
  (* search found nothing *)
  destruct (IHframes unwind_result _ _ _ H6).
   (* the search does eventually find something *)
   left. intros.
   assert (sat (this_allowance :*: r) ex_assertion). auto.
   assert (safe_frame_stack preclasses privclasses classes frames' (this_allowance :*: r :*: caller_allowance)).
    apply H. eauto.
   assert (this_allowance :*: r :*: caller_allowance <: r :*: current_allowance).
    rewrite <- combine_assoc. rewrite combine_symm. rewrite <- combine_assoc. apply combine_order.
     apply leq_refl. reflexivity.
     rewrite combine_symm. apply H16.
   eapply safe_frame_stack_leq. apply H2. apply H3.
   (* search fell off the end *)
   right. assumption.
  (* search failed *)
  discriminate.
Save.

Hint Unfold method_grants_ok.

Lemma unwind_stack_prop2 : forall classes frames frames' ref exc_cls a pc exsures code method stk lvars class cert caller_allowance ensures_internal this_allowance total_allowance cpa,
 E.unwind_stack classes (RT.mkFrame stk lvars pc code method class::frames) ref exc_cls = Some frames' ->
 verified_code (C.class_constantpool class) cpa ensures_internal exsures code cert ->
 constantpool_additional_correct preclasses classes (C.class_name class) (C.class_constantpool class) cpa ->
 this_allowance :*: caller_allowance <: total_allowance ->
 method_grants_ok privclasses (C.class_name class) method ensures_internal ->
 safe_frame_stack_rest preclasses privclasses classes frames (snd (fst (method_spec method))) exsures caller_allowance ->
 exception_handlers_assertion cert exsures pc (C.code_exception_table code) a ->
 sat this_allowance a ->
   safe_frame_stack preclasses privclasses classes frames' total_allowance
 \/frames' = nil.
intros classes frames frames' ref exc_cls a pc exsures code method stk lvars class cert caller_allowance ensures_internal this_allowance total_allowance cpa.
intros unwind_result code_verified cpa_ok this_p_caller_leq_total grants_ok frames_safe eha this_allowance_a.
simpl in unwind_result.
destruct (search_handlers_prop classes _ _ _ _ _ class exc_cls eha)
       as [[pc' [a' [search_result [lookup_res ex_assertion_implies_a]]]]
          | [ [search_result a_implies_exsures]
            | search_result ]]; rewrite search_result in unwind_result.
 (* found a handler in this method *)
 left. inversion unwind_result. subst. eapply mk_safe_current_frame; eauto.
 (* searched callers for a handler *)
 destruct (unwind_stack_prop _ _ _ _ _ _ _ _ unwind_result frames_safe).
  (* found one *)
  left. eauto using safe_frame_stack_leq.
  (* fell off the end *)
  right. assumption.
 (* searching the handlers failed *)
 discriminate.
Save.

(** Note that the pre-state s in the result doesn't have to be the current
    state.  The result may refer to an earlier pre-state with the same resource
    limit, saving some work in the later proofs. *)

Lemma throw_exception_prop : forall classes ref result allowance heap statics frames (used_res:RA.res) stk lvars pc code method class a this_allowance caller_allowance exsures cert ensures_internal current_allowance cpa,
 E.throw_exception (RT.mkState (RT.mkFrame stk lvars pc code method class::frames) classes heap statics used_res allowance) ref = result ->
 verified_code (C.class_constantpool class) cpa ensures_internal exsures code cert ->
 constantpool_additional_correct preclasses classes (C.class_name class) (C.class_constantpool class) cpa ->
 this_allowance :*: caller_allowance <: current_allowance ->
 method_grants_ok privclasses (C.class_name class) method ensures_internal ->
 safe_frame_stack_rest preclasses privclasses classes frames (snd (fst (method_spec method))) exsures caller_allowance ->
 exception_handlers_assertion cert exsures pc (C.code_exception_table code) a ->
 sat this_allowance a ->
 used_res :*: current_allowance <: allowance ->
 all_classes_verified preclasses privclasses classes ->
 all_preclasses_verified preclasses privclasses classes ->
 forall s, RT.state_reslimit res s = allowance ->
 safe_result s result.
Proof.
unfold safe_result.
intros classes ref result allowance heap statics frames used_res stk lvars pc code method class a this_allowance caller_allowance exsures cert ensures current_allowance cpa.
intros EXEC code_verified cpa_ok this_p_caller_leq_allowance grants_ok frames_safe eha this_allowance_a used_p_current_leq_allowance all_classes_v all_preclasses_v s s_allowance.
unfold E.throw_exception in EXEC.
destruct (RT.heap_lookup_class heap ref) as [[cls_nm _] | _]; try (right; right; right; assumption).
destruct (option_dec (E.unwind_stack classes (RT.mkFrame stk lvars pc code method class ::frames) ref cls_nm)) as [[frames' unwind_result] | unwind_result]; rewrite unwind_result in EXEC.
 (* unwinding succeeded *)
 destruct (unwind_stack_prop2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ unwind_result code_verified cpa_ok this_p_caller_leq_allowance grants_ok frames_safe eha this_allowance_a).
  (* and found a handler *)
  destruct (safe_frame_stack_has_frames _ _ _ H) as [f [fs frames_eq]]. subst frames'.
  left. eapply ex_intro. repeat split.
   apply EXEC.
   eapply mk_safe_state; eassumption.
   left; rewrite s_allowance; reflexivity.
  (* no handler found *)
  subst frames'.
  right. right. left. eapply ex_intro. eapply ex_intro. repeat split.
   eassumption.
   left; rewrite s_allowance; reflexivity.
   simpl. rewrite <- (r_combine_e used_res). eapply leq_trans.
    apply combine_order.
     apply leq_refl. reflexivity.
     eapply e_bottom.
    apply used_p_current_leq_allowance.
 (* unwinding failed *)
 right. right. right. assumption.
Save.

Lemma throw_builtin_exception_ok : forall classes stk lvars pc code method class frames heap static_fields (used_res:RA.res) exn result allowance a
                                          current_allowance this_allowance exsures cert caller_allowance ensures_internal cpa,
 E.throw_builtin_exception (RT.mkState (RT.mkFrame stk lvars pc code method class :: frames) classes heap static_fields used_res allowance) exn = result ->
 verified_code (C.class_constantpool class) cpa ensures_internal exsures code cert ->
 constantpool_additional_correct preclasses classes (C.class_name class) (C.class_constantpool class) cpa ->
 this_allowance :*: caller_allowance <: current_allowance ->
 method_grants_ok privclasses (C.class_name class) method ensures_internal ->
 safe_frame_stack_rest preclasses privclasses classes frames (snd (fst (method_spec method))) exsures caller_allowance ->
 exception_handlers_assertion cert exsures pc (C.code_exception_table code) a ->
 sat this_allowance (R_tensor (CP.builtin_exception_to_class_name exn) a) ->
 used_res :*: current_allowance <: allowance ->
 all_classes_verified preclasses privclasses classes ->
 all_preclasses_verified preclasses privclasses classes ->
 forall s, RT.state_reslimit res s = allowance ->
 safe_result s result.
Proof.
unfold safe_result.
intros classes stk lvars pc code method class frames heap static_fields used_res exn result allowance a.
intros current_allowance this_allowance exsures cert caller_allowance ensures cpa.
intros EXEC code_verified cpa_ok this_p_caller_leq_current grants_ok frames_safe eha sat_a used_p_current_leq_tot all_classes_v all_preclasses_v s s_allowance.
unfold E.throw_builtin_exception in EXEC.
destruct (CP.gather_class_exists_evidence classes (CP.builtin_exception_to_class_name exn)).
 right; right; right; assumption.
 destruct (RT.heap_new heap (CP.builtin_exception_to_class_name exn) e0)
       as [heap' addr [H1 [H2 [H3 [preserve H4]]]]].
 simpl E.add_res_new in EXEC.
 unfold R_tensor in *.
 destruct (r_new (CP.builtin_exception_to_class_name exn)) as [r|] _eqn: exn_r.
  destruct (r_new_match _ _ exn_r) as [a_r [exn_a_r exn_a_r']].
  rewrite exn_a_r in sat_a.
  destruct sat_a as [r1 [r2 [r1r2_this_allowance [exn_r1 r2_a]]]]. fold sat in r2_a.
  eapply throw_exception_prop.
   apply EXEC.
   apply code_verified.
   apply cpa_ok.
   apply (leq_refl (r2 :*: caller_allowance)). reflexivity.
   assumption.
   apply frames_safe.
   apply eha.
   apply r2_a.
   rewrite combine_assoc. rewrite <- (combine_assoc used_res r r2).
   rewrite <- exn_a_r'.
   rewrite exn_r1; try (apply leq_refl; reflexivity).
   rewrite r1r2_this_allowance; try (apply leq_refl; reflexivity).
   rewrite <- combine_assoc.
   rewrite this_p_caller_leq_current; try (apply leq_refl; reflexivity).
   assumption.
   assumption.
   assumption.
   assumption.
  rewrite (r_new_empty _ exn_r) in sat_a.
  eapply throw_exception_prop.
   apply EXEC.
   apply code_verified.
   apply cpa_ok.
   apply (leq_refl (this_allowance :*: caller_allowance)). reflexivity.
   assumption.
   apply frames_safe.
   apply eha.
   assumption.
   rewrite this_p_caller_leq_current.
   assumption.
   assumption.
   assumption.
   assumption.
Save.

(** ** Relate old and new resource limits. *)

Lemma update_reslimit_ok : forall class method r old_reslimit new_reslimit Q',
  E.update_reslimit privclasses class method old_reslimit = new_reslimit ->
  method_grants_ok privclasses (C.class_name class) method Q' ->
  sat r Q' ->
  exists r',
     (old_reslimit = new_reslimit \/ CLSNM.In (C.class_name class) privclasses)
  /\ sat (r :*: r') (snd (fst (method_spec method)))
  /\ old_reslimit :*: r' <: new_reslimit.
Proof.
 intros until Q'. intros EXEC verified Q'sat.
 unfold E.update_reslimit in EXEC.
 case_eq (ANN.GA.A.grants (C.method_annot method)).
  intros g geq. rewrite geq in EXEC.
  case_eq (E.ClassnameSet.mem (C.class_name class) privclasses).
   intro priveq. rewrite priveq in EXEC.
   exists (res_parse g).
   repeat split.
    right. auto using CLSNM.mem_2.
    destruct verified as [[g' [grants [priv post]]]|[grants post]]; change ANN.grants with ANN.GA.A.grants in grants.
     rewrite grants in geq. injection geq as geq'. subst g'.
     rewrite post in Q'sat. simpl in Q'sat. apply Q'sat. apply res_formula.
     rewrite grants in geq. discriminate. 
    rewrite <- EXEC. apply leq_refl. reflexivity.
   intro bad. destruct verified as [[_ [_ [priv _]]]|[nogrants _]].
    apply E.ClassnameSet.mem_1 in priv. rewrite priv in bad. discriminate.
    change ANN.grants with ANN.GA.A.grants in nogrants.
    rewrite nogrants in geq. discriminate.
   intros geq. rewrite geq in EXEC. exists e. repeat split.
    left; assumption.
    destruct verified as [[g' [grants [priv post]]]|[grants post]]; change ANN.grants with ANN.GA.A.grants in grants.
     rewrite grants in geq. discriminate.
     rewrite <- post. eapply sat_leq. apply Q'sat. apply leq_refl. rewrite r_combine_e. reflexivity.
   apply leq_refl. rewrite EXEC. rewrite r_combine_e. reflexivity.
Qed.

Opaque E.stack_to_lvars.
Opaque E.throw_builtin_exception.
Opaque E.throw_exception.

(** ** Main safety result.
    Executing a step from a safe state yields a safe result. *)

Hint Resolve mk_safe_state mk_safe_current_frame no_allowance_change.

Theorem safety : forall s result,
 safe_state preclasses privclasses s ->
 E.exec preclasses privclasses s = result ->
 safe_result s result.
Proof.
unfold safe_result.
intros s result s_safefor_allowance EXEC.
destruct s_safefor_allowance as [fs classes heap static_fields total_allowance current_allowance consumed
                                 leq_total_allowance fs_safe all_classes_v all_preclasses_v].
destruct fs_safe as [classes stk lvars class method code pc this_allowance cert pre_condition ensures_internal ensures ex_ensures caller_allowance current_allowance fs cpa
                    code_verified cpa_ok pc_has_precond allowance_sat_precond this_p_caller_leq_current grants_ok ensures_spec fs_safe].
set (code_verified_copy:=code_verified). generalize code_verified_copy. clear code_verified_copy. intro.
destruct code_verified as [cert_covers_code instrs_verified].

(* deduce that the current pc points to a real instruction *)
assert (H:exists op, nth_error (C.code_code code) pc = Some op).
 apply nth_error_ok. eapply cert_covers_code. apply pc_has_precond.
destruct H as [op op_exists].

(* further deduce that this instruction has been verified *)
assert (op_verified:verified_instruction (C.class_constantpool class) cpa ensures_internal ex_ensures cert (C.code_exception_table code) op pc).
 auto.
destruct op_verified as [a1 a2 cert_a op_precond precond_implies_real_a].
change Cert.lookup with CERT.Cert.lookup in cert_a.
rewrite pc_has_precond in cert_a. inversion cert_a. subst a1. clear cert_a.

clear cert_covers_code. clear instrs_verified.

assert (this_sat_a:sat this_allowance a2) by (apply implies_soundness with pre_condition; auto).
clear precond_implies_real_a.

(* find out what we are really doing here *)
simpl in EXEC. rewrite op_exists in EXEC. destruct op; inversion op_precond; clear op_precond.

(* op_iarithb *)
subst i pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
destruct op; try (decompose [or] H1; discriminate); try (right; right; right; assumption);
intuition eauto 7.

(* op_iarithu *)
subst i pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
destruct op; try (right; right; right; assumption);
intuition eauto 7.

(* op_dup *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r); try (right; right; right; assumption).
intuition eauto 7.

(* op_dup_x1 *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r); try (right; right; right; assumption).
destruct (RT.val_category r0); try (right; right; right; assumption).
intuition eauto 7.

(* op_dup_x2 *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r); try (right; right; right; assumption).
destruct (RT.val_category r0); try (right; right; right; assumption).
 destruct stk; try (right; right; right; assumption).
  destruct (RT.val_category r1); try (right; right; right; assumption).
  intuition eauto 7.
 intuition eauto 7.

(* op_dup2 *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r); try (right; right; right; assumption).
 destruct stk; try (right; right; right; assumption). intuition eauto 7.
 intuition eauto 7.

(* op_dup2_x1 *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r); try (right; right; right; assumption).
 destruct stk; try (right; right; right; assumption). intuition eauto 7.
 intuition eauto 7.

(* op_dup2_x2 *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r0); try (right; right; right; assumption).
 destruct stk; try (right; right; right; assumption).
  destruct (RT.val_category r); try (right; right; right; assumption).
   destruct (RT.val_category r1); try (right; right; right; assumption).
    destruct stk; try (right; right; right; assumption).
     destruct (RT.val_category r2); try (right; right; right; assumption).
      intuition eauto 7.
    intuition eauto 7.
   destruct (RT.val_category r1); try (right; right; right; assumption).
    intuition eauto 7.
 destruct (RT.val_category r); try (right; right; right; assumption).
  intuition eauto 7.

(* op_nop *)
subst pc0 a2. simpl in EXEC. intuition eauto 7.

(* op_pop *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r); try (right; right; right; assumption).
intuition eauto 7.

(* op_pop2 *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r); try (right; right; right; assumption).
 destruct stk; try (right; right; right; assumption). intuition eauto 7.
 intuition eauto 7.

(* op_swap *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct (RT.val_category r); try (right; right; right; assumption).
destruct (RT.val_category r0); try (right; right; right; assumption).
intuition eauto 7.

(* op_load *)
subst s n0 pc0 a2. simpl in EXEC.
destruct (option_mult (nth_error lvars n)); try (right; right; right; assumption).
intuition eauto 7.

(* op_store *)
subst s n0 pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct (E.update_lvars n r lvars); try (right; right; right; assumption).
intuition eauto 7.

(* op_instanceof *)
subst t pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
rewrite H1 in EXEC.

assert (exists classes', exists p : CP.preserve_old_classes classes classes', exists o, exists c, exists H, E.R.resolve_class (C.class_name class) clsnm classes preclasses = CP.load_ok _ p o c H).
 destruct H2.
  destruct (cpa_classref _ _ _ _ _ cpa_ok idx clsnm H1 H) as [classes' [p [oa [c [c_exists resolve_ok]]]]]. intuition eauto 6.
  destruct (cpa_ins_class _ _ _ _ _ cpa_ok idx clsnm H1 H) as [classes' [p [oa [c [c_exists [resolve_ok _]]]]]]. intuition eauto 6.
destruct H as [classes' [p [oa [c [H resolve_ok]]]]].

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

rewrite resolve_ok in EXEC.
destruct o.
 (* nonnull pointer *)
 match goal with _:match ?x with inleft _ => _ | inright _ => _ end = _ |- _ => destruct x end.
  destruct s. destruct (A.is_assignable classes' (C.ty_obj x) (C.ty_obj clsnm)).
   left. eapply ex_intro. repeat split.
    eassumption.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
     eapply preserve_constantpool_additional_correct; eauto.
     eapply preserve_safe_frame_stack_rest; eauto.
    auto.
   left. eapply ex_intro. repeat split.
    eassumption.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
     eapply preserve_constantpool_additional_correct; eauto.
     eapply preserve_safe_frame_stack_rest; eauto.
    auto.
  right. right. right. assumption.
 (* null pointer *)
 left. eapply ex_intro. repeat split.
  eassumption.
  eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
   eapply preserve_constantpool_additional_correct; eauto.
   eapply preserve_safe_frame_stack_rest; eauto.
  auto.

(* op_invokeinterface *)
(* NB: this is essentially the same as invokevirtual, below *)
subst t pc0 a2. simpl in EXEC.
rewrite H1 in EXEC.

destruct (B.Methodname.eq_dec mn B.init) as [_|mn_neq_init].
 right. right. right. assumption.

destruct (cpa_interface_method _ _ _ _ _ cpa_ok _ _ _ _ _ _ _ H1 H2)
      as [classes' [p [oa [c [m [[X1 [X2 X3]] [resolve_ok [not_static has_spec]]]]]]]].

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

rewrite resolve_ok in EXEC.
rewrite not_static in EXEC.

destruct this_sat_a as [this_sat_normal [this_sat_null [this_sat_absmeth this_sat_incompat]]]. fold sat in *.

destruct (E.pop_n (length (C.descriptor_arg_types md)) stk) as [[args op_stack] | ]; try (right; right; right; assumption).
destruct op_stack; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
destruct o.
 (* nonnull pointer *)
 destruct (RT.heap_lookup_class (RT.preserve_cert_heap heap p) a0) as [[cls_nm addr_is_cls_nm] | _]; try (right; right; right; assumption).

 destruct (A.is_assignable classes' (C.ty_obj cls_nm) (C.ty_obj clsnm)) as [cls_nm_sub_clsnm|]; try (right; right; right; assumption).

 match goal with _:match ?x with Some _ => _ | None => _ end = _ |- _ =>
   destruct x as [[c' m' [cl_loaded [m'_exists [c'_class [m'_not_static [cls_sub_c' lookup_min]]]]]]|]
 end.
  (* method found *)
  destruct (C.method_abstract m') as [] _eqn: not_abstract.
   (* the found method was abstract *)
   eapply throw_builtin_exception_ok; eauto.
    eapply preserve_constantpool_additional_correct; eauto.
    rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.
   (* we're ok: the found method wasn't abstract *)
   destruct (all_classes_v' _ _ cl_loaded c'_class) as [cpa' cpa'_ok methods_ok _ _].
   simpl in *.

   assert (exists cA, CP.class_loaded classes' cls_nm cA /\ C.class_interface cA = false).
    eapply RT.object_class_implies_class_exists; eassumption.
   destruct H as [cA [cls_nm_loaded cls_nm_class]].
  
   assert (safe_over : safe_override (method_spec m') (method_spec m)).
    eapply virtual_method_lookup_matches_specification.
     change mn with (fst (mn,md)) in mn_neq_init. eassumption.
     apply all_classes_v'.
     apply X1.
     eassumption.
     apply not_static.
     apply X3.
     apply cl_loaded.
     assumption.
     assumption.
     assumption.
     apply cls_nm_loaded.
     apply cls_nm_class.
     assumption.
     assumption.
     assumption.

   destruct (methods_ok _ _ m'_exists) as [[code' method_ok]|[code_res abs_or_nat]].
    assert (exists Pm', exists Qm', exists Xm', method_spec m' = (Pm', Qm', Xm')). destruct m'. destruct method_annot. destruct method_spec0 as [[P'' Q''] X'']. exists P''. exists Q''. exists X''. simpl. eauto.
    destruct H as [Pm' [Qm' [Xm' m'_has_spec]]].
    destruct (method_ok _ _ _ m'_has_spec) as [cert' [P'' [Q'' [m'_has_code [grants [code_verified [P'_P'' cert_P'']]]]]]].
    simpl in *. rewrite m'_has_code in EXEC.
(*   destruct (option_dec (C.method_code m')) as [[code' code_res]|code_res]; rewrite code_res in EXEC; try (right; right; right; assumption).*)
    destruct (E.stack_to_lvars (RT.rt_addr (Some a0) :: rev args) (C.code_max_lvars code')); try (right; right; right; assumption).
  
    destruct this_sat_normal as [r1 [r2 [r1r2_this [r1_P [r2_Qa r2_Xa']]]]].
    rewrite m'_has_spec in safe_over. rewrite has_spec in safe_over. destruct safe_over as [P_Pm' [Qm'_Q Xm'_X]].

    assert (r1 :*: (r2 :*: caller_allowance) <: current_allowance(*this_allowance :*: caller_allowance*)).
    rewrite combine_assoc. rewrite r1r2_this; try (apply leq_refl; reflexivity). assumption.

   assert (sat r1 P'') by auto.

   left. eapply ex_intro. repeat split.
    apply EXEC.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
     eapply safe_stack_cons; eauto.
      eapply preserve_safe_frame_stack_rest; eassumption.
      eapply preserve_constantpool_additional_correct; eassumption.
      rewrite m'_has_spec. auto.
      apply leq_refl. reflexivity.
     auto.
  (* native method *)
 destruct abs_or_nat as [abs|[native native_priv]].
  rewrite not_abstract in abs; discriminate.
  rewrite code_res in EXEC.
   set (s0 := (RT.mkState (A:=RA.res) (RT.mkFrame op_stack lvars pc code method class :: fs) classes'
                (RT.preserve_cert_heap heap p)
                (RT.preserve_cert_fieldstore_over_classes static_fields p)
                consumed total_allowance)) in EXEC.
   assert (exec_safe : safe_state preclasses privclasses s0).
    unfold s0.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
    eapply preserve_constantpool_additional_correct; eassumption.
    eapply preserve_safe_frame_stack_rest; eassumption.
   eapply unchanging_allowance_ok with (s:=s0).
    intros. inversion H; subst; [apply no_allowance_change|apply priv_allowance_change]; auto.
   destruct (SNM.NM.native_invoke c' m' (RT.rt_addr (Some a0) :: rev args) s0) as [native_result|] _eqn: native_eq.
   destruct this_sat_normal as [r1 [r2 [r1r2_ok [P_ok [Q_ok X_ok]]]]].
   assert (rem_ok : RT.state_res _ s0 :*: r1 :*: (r2 :*: caller_allowance) <: total_allowance) by
     (simpl; rewrite combine_assoc; rewrite <- (combine_assoc consumed); rewrite r1r2_ok;
       rewrite <- combine_assoc; rewrite this_p_caller_leq_current; assumption).
   assert (newspec : exists P', exists Q', exists X', method_spec m' = (P', Q', X')) by
     (destruct (method_spec m') as [[p' q'] x']; exists p'; exists q'; exists x'; reflexivity).
   destruct newspec as [P' [Q' [X' has_spec']]].
   rewrite has_spec, has_spec' in safe_over. destruct safe_over as [P'ok [Q'ok X'ok]].
   destruct (SNM.safe_native preclasses privclasses _ _ _ _ _ P' Q' X' r1 (r2 :*: caller_allowance) exec_safe cl_loaded native has_spec' native_eq (P'ok _ P_ok) rem_ok) as [r' [post_cond [r'_ok [pres [only nolimchange]]]]]; auto.
   destruct native_result. destruct resval; simpl in *.
     left. match type of EXEC with JVM.cont ?S = result => exists S end.
     repeat split; auto.
     eapply mk_safe_state; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite <- combine_assoc in r'_ok. apply r'_ok.
     eapply mk_safe_current_frame; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite (combine_symm r2 r'). rewrite <- (combine_assoc r'). reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.

     left. match type of EXEC with JVM.cont ?S = result => exists S end.
     repeat split; auto.
     eapply mk_safe_state; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite <- combine_assoc in r'_ok. apply r'_ok.
     eapply mk_safe_current_frame; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite (combine_symm r2 r'). rewrite <- (combine_assoc r'). reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     
     eapply throw_exception_prop.
       apply EXEC.
       apply code_verified_copy.
       eapply preserve_constantpool_additional_correct; eauto.
       eauto using CP.preserve_old_classes_trans.
       eauto using CP.compose_only_add.
       apply (leq_refl ((r2:*:r') :*: caller_allowance)). reflexivity.
       apply grants_ok.
       rewrite ensures_spec. eauto using preserve_safe_frame_stack_rest.
       eassumption.
       apply X_ok. apply X'ok. apply post_cond.
       simpl in *. rewrite combine_assoc. rewrite (combine_symm r2 r'). rewrite combine_assoc. rewrite <- combine_assoc. assumption.
       eapply preserve_all_classes_verified; eauto.
       eapply preserve_all_preclasses_verified; eauto.
       simpl. apply nolimchange.

   right; right; right; assumption.
  (* method not found *)
  eapply throw_builtin_exception_ok; eauto.
   eapply preserve_constantpool_additional_correct; eauto.
   rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.
 (* class of object in heap can't be assigned to interface *)
  eapply throw_builtin_exception_ok; eauto.
   eapply preserve_constantpool_additional_correct; eauto.
   rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.
 (* null pointer *)
 eapply throw_builtin_exception_ok; eauto.
  eapply preserve_constantpool_additional_correct; eauto.
  rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.

(* op_invokespecial *)
subst t pc0 a2. simpl in EXEC.
rewrite H1 in EXEC.

destruct (cpa_instance_special_method _ _ _ _ _ cpa_ok _ _ _ _ _ _ _ H1 H2)
      as [classes' [p [oa [c [m [[X1 [X2 X3]] [resolve_ok [not_abstract [not_static [has_spec not_interface]]]]]]]]]].
change R.resolve_method with E.R.resolve_method in resolve_ok.

rewrite resolve_ok in EXEC.
destruct (E.pop_n (length (C.descriptor_arg_types md)) stk) as [[args op_stack] | ]; try (right; right; right; assumption).
destruct op_stack; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

destruct this_sat_a as [this_sat_nonnull this_sat_null]. fold sat in *.

destruct o.
 (* nonnull pointer *)
 rewrite not_static in EXEC.
 rewrite not_abstract in EXEC.
 destruct (all_classes_v' _ _ X1 not_interface) as [cpa' cpa'_ok methods_ok].
 destruct (methods_ok _ _ X2) as [[m_code method_ok]|[no_code abs_or_nat]]. 
  destruct this_sat_nonnull as [r1 [r2 [r1r2_this [r1_P [r2_Qa r2_Xa']]]]].

  assert (r1 :*: (r2 :*: caller_allowance) <: current_allowance(*this_allowance :*: caller_allowance*)).
  rewrite combine_assoc. rewrite r1r2_this; try (apply leq_refl; reflexivity). assumption.

  destruct (method_ok _ _ _ has_spec) as [cert' [P' [Q' [has_code [grants [code_verified [P_P' cert_P']]]]]]].
  simpl in *. rewrite has_code in EXEC.

  destruct (E.stack_to_lvars (RT.rt_addr (Some a0)::rev args) (C.code_max_lvars m_code)); try (right; right; right; assumption).

  assert (sat r1 P') by auto.

  left. eapply ex_intro. repeat split.
   apply EXEC.
   eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
    eapply safe_stack_cons; eauto.
     eapply preserve_safe_frame_stack_rest; eassumption.
     eapply preserve_constantpool_additional_correct; eassumption.
     rewrite has_spec. assumption.
     apply leq_refl. reflexivity.
   auto.

  simpl in *. rewrite no_code in EXEC.
  destruct abs_or_nat as [abs|[native native_priv]].
   rewrite not_abstract in abs; discriminate.
   set (s0 := (RT.mkState (A:=RA.res) (RT.mkFrame op_stack lvars pc code method class :: fs) classes'
                (RT.preserve_cert_heap heap p)
                (RT.preserve_cert_fieldstore_over_classes static_fields p)
                consumed total_allowance)) in EXEC.
   assert (exec_safe : safe_state preclasses privclasses s0).
    unfold s0.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
    eapply preserve_constantpool_additional_correct; eassumption.
    eapply preserve_safe_frame_stack_rest; eassumption.
   eapply unchanging_allowance_ok with (s:=s0).
    intros. inversion H; subst; [apply no_allowance_change|apply priv_allowance_change]; auto.
   destruct (SNM.NM.native_invoke c m (RT.rt_addr (Some a0) :: rev args) s0) as [native_result|] _eqn: native_eq.
   destruct this_sat_nonnull as [r1 [r2 [r1r2_ok [P_ok [Q_ok X_ok]]]]].
   assert (rem_ok : RT.state_res _ s0 :*: r1 :*: (r2 :*: caller_allowance) <: total_allowance) by
     (simpl; rewrite combine_assoc; rewrite <- (combine_assoc consumed); rewrite r1r2_ok;
       rewrite <- combine_assoc; rewrite this_p_caller_leq_current; assumption).
   destruct (SNM.safe_native preclasses privclasses _ _ _ _ _ P Q X r1 (r2 :*: caller_allowance) exec_safe X1 native has_spec native_eq P_ok rem_ok) as [r' [post_cond [r'_ok [pres [only nolimchange]]]]]; auto.
   destruct native_result. destruct resval; simpl in *.
     left. match type of EXEC with JVM.cont ?S = result => exists S end.
     repeat split; auto.
     eapply mk_safe_state; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite <- combine_assoc in r'_ok. apply r'_ok.
     eapply mk_safe_current_frame; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite (combine_symm r2 r'). rewrite <- (combine_assoc r'). reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.

     left. match type of EXEC with JVM.cont ?S = result => exists S end.
     repeat split; auto.
     eapply mk_safe_state; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite <- combine_assoc in r'_ok. apply r'_ok.
     eapply mk_safe_current_frame; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite (combine_symm r2 r'). rewrite <- (combine_assoc r'). reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     
     eapply throw_exception_prop.
       apply EXEC.
       apply code_verified_copy.
       eapply preserve_constantpool_additional_correct; eauto.
       eauto using CP.preserve_old_classes_trans.
       eauto using CP.compose_only_add.
       apply (leq_refl ((r2:*:r') :*: caller_allowance)). reflexivity.
       apply grants_ok.
       rewrite ensures_spec. eauto using preserve_safe_frame_stack_rest.
       eassumption.
       apply X_ok. apply post_cond.
       simpl in *. rewrite combine_assoc. rewrite (combine_symm r2 r'). rewrite combine_assoc. rewrite <- combine_assoc. assumption.
       eapply preserve_all_classes_verified; eauto.
       eapply preserve_all_preclasses_verified; eauto.
       simpl. apply nolimchange.

   right; right; right; assumption.
     
 (* null pointer *)
 eapply throw_builtin_exception_ok; eauto.
  eapply preserve_constantpool_additional_correct; eauto.
  rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.

(* op_invokestatic *)
subst t pc0 a2. simpl in EXEC.
rewrite H1 in EXEC.

destruct (E.pop_n (length (C.descriptor_arg_types md)) stk) as [[args op_stack] | ]; try (right; right; right; assumption).

destruct (cpa_static_method _ _ _ _ _ cpa_ok _ _ _ _ _ _ _ H1 H2)
      as [classes' [p [oa [c [m [[X1 [X2 X3]] [resolve_ok [static [has_spec [not_interface not_abstract]]]]]]]]]].

rewrite resolve_ok in EXEC.
rewrite static in EXEC.

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

destruct (all_classes_v' _ _ X1 not_interface) as [cpa' cpa'_ok methods_ok].
destruct (methods_ok _ _ X2) as [[m_code method_ok]|[no_code abs_or_nat]]. 
 destruct (method_ok _ _ _ has_spec) as [cert' [P' [Q' [has_code [grants [code_verified [P_P' cert_P']]]]]]].
 simpl in *. rewrite has_code in EXEC.

 destruct (E.stack_to_lvars (rev args) (C.code_max_lvars m_code)); try (right; right; right; assumption).

 destruct this_sat_a as [r1 [r2 [r1r2_this [r1_P [r2_Qa r2_Xa']]]]]. fold sat in *.

 simpl in *.

 assert (r1 :*: (r2 :*: caller_allowance) <: current_allowance).
 rewrite combine_assoc. rewrite r1r2_this; try (apply leq_refl; reflexivity). assumption.

 assert (sat r1 P') by auto.

 left. eapply ex_intro. repeat split.
  eassumption.
  eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
   eapply safe_stack_cons; eauto.
    eapply preserve_safe_frame_stack_rest; eassumption.
    eapply preserve_constantpool_additional_correct; eassumption.
    rewrite has_spec. assumption.
    apply leq_refl. reflexivity.
   auto.

  simpl in *. rewrite no_code in EXEC.
  destruct abs_or_nat as [abs|[native native_priv]].
   rewrite not_abstract in abs; discriminate.
   set (s0 := (RT.mkState (A:=RA.res) (RT.mkFrame op_stack lvars pc code method class :: fs) classes'
                (RT.preserve_cert_heap heap p)
                (RT.preserve_cert_fieldstore_over_classes static_fields p)
                consumed total_allowance)) in EXEC.
   assert (exec_safe : safe_state preclasses privclasses s0).
    unfold s0.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
    eapply preserve_constantpool_additional_correct; eassumption.
    eapply preserve_safe_frame_stack_rest; eassumption.
   eapply unchanging_allowance_ok with (s:=s0).
    intros. inversion H; subst; [apply no_allowance_change|apply priv_allowance_change]; auto.
   destruct (SNM.NM.native_invoke c m (rev args) s0) as [native_result|] _eqn: native_eq.
   destruct this_sat_a as [r1 [r2 [r1r2_ok [P_ok [Q_ok X_ok]]]]].
   assert (rem_ok : RT.state_res _ s0 :*: r1 :*: (r2 :*: caller_allowance) <: total_allowance) by
     (simpl; rewrite combine_assoc; rewrite <- (combine_assoc consumed); rewrite r1r2_ok;
       rewrite <- combine_assoc; rewrite this_p_caller_leq_current; assumption).
   destruct (SNM.safe_native preclasses privclasses _ _ _ _ _ P Q X r1 (r2 :*: caller_allowance) exec_safe X1 native has_spec native_eq P_ok rem_ok) as [r' [post_cond [r'_ok [pres [only nolimchange]]]]]; auto.
   destruct native_result. destruct resval; simpl in *.
     left. match type of EXEC with JVM.cont ?S = result => exists S end.
     repeat split; auto.
     eapply mk_safe_state; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite <- combine_assoc in r'_ok. apply r'_ok.
     eapply mk_safe_current_frame; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite (combine_symm r2 r'). rewrite <- (combine_assoc r'). reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.

     left. match type of EXEC with JVM.cont ?S = result => exists S end.
     repeat split; auto.
     eapply mk_safe_state; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite <- combine_assoc in r'_ok. apply r'_ok.
     eapply mk_safe_current_frame; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite (combine_symm r2 r'). rewrite <- (combine_assoc r'). reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     
     eapply throw_exception_prop.
       apply EXEC.
       apply code_verified_copy.
       eapply preserve_constantpool_additional_correct; eauto.
       eauto using CP.preserve_old_classes_trans.
       eauto using CP.compose_only_add.
       apply (leq_refl ((r2:*:r') :*: caller_allowance)). reflexivity.
       apply grants_ok.
       rewrite ensures_spec. eauto using preserve_safe_frame_stack_rest.
       eassumption.
       apply X_ok. apply post_cond.
       simpl in *. rewrite combine_assoc. rewrite (combine_symm r2 r'). rewrite combine_assoc. rewrite <- combine_assoc. assumption.
       eapply preserve_all_classes_verified; eauto.
       eapply preserve_all_preclasses_verified; eauto.
       simpl. apply nolimchange.

   right; right; right; assumption.

(* op_invokevirtual *)
subst t pc0 a2. simpl in EXEC.
rewrite H1 in EXEC.

destruct (B.Methodname.eq_dec mn B.init) as [_|mn_neq_init].
 right. right. right. assumption.

destruct (cpa_instance_method _ _ _ _ _ cpa_ok _ _ _ _ _ _ _ H1 H2)
      as [classes' [p [oa [c [m [[X1 [X2 X3]] [resolve_ok [not_static has_spec]]]]]]]].

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

rewrite resolve_ok in EXEC.
rewrite not_static in EXEC.

destruct this_sat_a as [this_sat_normal [this_sat_null this_sat_absmeth]]. fold sat in *.

destruct (E.pop_n (length (C.descriptor_arg_types md)) stk) as [[args op_stack] | ]; try (right; right; right; assumption).
destruct op_stack; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
destruct o.
 (* nonnull pointer *)
 destruct (RT.heap_lookup_class (RT.preserve_cert_heap heap p) a0) as [[cls_nm addr_is_cls_nm] | _]; try (right; right; right; assumption).

 destruct (A.is_assignable classes' (C.ty_obj cls_nm) (C.ty_obj clsnm)) as [cls_nm_sub_clsnm|]; try (right; right; right; assumption).

 match goal with _:match ?x with Some _ => _ | None => _ end = _ |- _ =>
   destruct x as [[c' m' [cl_loaded [m'_exists [c'_class [m'_not_static [cls_sub_c' lookup_min]]]]]]|]
 end.
  (* method found *)
  destruct (C.method_abstract m') as [] _eqn: not_abstract.
   (* the found method was abstract *)
   eapply throw_builtin_exception_ok; eauto.
    eapply preserve_constantpool_additional_correct; eauto.
    rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.
   (* we're ok: the found method wasn't abstract *)
   destruct (all_classes_v' _ _ cl_loaded c'_class) as [cpa' cpa'_ok methods_ok _ _].
   simpl in *.

   assert (exists cA, CP.class_loaded classes' cls_nm cA /\ C.class_interface cA = false).
    eapply RT.object_class_implies_class_exists; eassumption.
   destruct H as [cA [cls_nm_loaded cls_nm_class]].
  
   assert (safe_over : safe_override (method_spec m') (method_spec m)).
    eapply virtual_method_lookup_matches_specification.
     change mn with (fst (mn,md)) in mn_neq_init. eassumption.
     apply all_classes_v'.
     apply X1.
     eassumption.
     apply not_static.
     apply X3.
     apply cl_loaded.
     assumption.
     assumption.
     assumption.
     apply cls_nm_loaded.
     apply cls_nm_class.
     assumption.
     assumption.
     assumption.

   destruct (methods_ok _ _ m'_exists) as [[code' method_ok]|[code_res abs_or_nat]].
    assert (exists Pm', exists Qm', exists Xm', method_spec m' = (Pm', Qm', Xm')). destruct m'. destruct method_annot. destruct method_spec0 as [[P'' Q''] X'']. exists P''. exists Q''. exists X''. simpl. eauto.
    destruct H as [Pm' [Qm' [Xm' m'_has_spec]]].
    destruct (method_ok _ _ _ m'_has_spec) as [cert' [P'' [Q'' [m'_has_code [grants [code_verified [P'_P'' cert_P'']]]]]]].
    simpl in *. rewrite m'_has_code in EXEC.
(*   destruct (option_dec (C.method_code m')) as [[code' code_res]|code_res]; rewrite code_res in EXEC; try (right; right; right; assumption).*)
    destruct (E.stack_to_lvars (RT.rt_addr (Some a0) :: rev args) (C.code_max_lvars code')); try (right; right; right; assumption).
  
    destruct this_sat_normal as [r1 [r2 [r1r2_this [r1_P [r2_Qa r2_Xa']]]]].
    rewrite m'_has_spec in safe_over. rewrite has_spec in safe_over. destruct safe_over as [P_Pm' [Qm'_Q Xm'_X]].

    assert (r1 :*: (r2 :*: caller_allowance) <: current_allowance(*this_allowance :*: caller_allowance*)).
    rewrite combine_assoc. rewrite r1r2_this; try (apply leq_refl; reflexivity). assumption.

   assert (sat r1 P'') by auto.

   left. eapply ex_intro. repeat split.
    apply EXEC.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
     eapply safe_stack_cons; eauto.
      eapply preserve_safe_frame_stack_rest; eassumption.
      eapply preserve_constantpool_additional_correct; eassumption.
      rewrite m'_has_spec. auto.
      apply leq_refl. reflexivity.
     auto.
  (* native method *)
 destruct abs_or_nat as [abs|[native native_priv]].
  rewrite not_abstract in abs; discriminate.
  rewrite code_res in EXEC.
   set (s0 := (RT.mkState (A:=RA.res) (RT.mkFrame op_stack lvars pc code method class :: fs) classes'
                (RT.preserve_cert_heap heap p)
                (RT.preserve_cert_fieldstore_over_classes static_fields p)
                consumed total_allowance)) in EXEC.
   assert (exec_safe : safe_state preclasses privclasses s0).
    unfold s0.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
    eapply preserve_constantpool_additional_correct; eassumption.
    eapply preserve_safe_frame_stack_rest; eassumption.
   eapply unchanging_allowance_ok with (s:=s0).
    intros. inversion H; subst; [apply no_allowance_change|apply priv_allowance_change]; auto.
   destruct (SNM.NM.native_invoke c' m' (RT.rt_addr (Some a0) :: rev args) s0) as [native_result|] _eqn: native_eq.
   destruct this_sat_normal as [r1 [r2 [r1r2_ok [P_ok [Q_ok X_ok]]]]].
   assert (rem_ok : RT.state_res _ s0 :*: r1 :*: (r2 :*: caller_allowance) <: total_allowance) by
     (simpl; rewrite combine_assoc; rewrite <- (combine_assoc consumed); rewrite r1r2_ok;
       rewrite <- combine_assoc; rewrite this_p_caller_leq_current; assumption).
   assert (newspec : exists P', exists Q', exists X', method_spec m' = (P', Q', X')) by
     (destruct (method_spec m') as [[p' q'] x']; exists p'; exists q'; exists x'; reflexivity).
   destruct newspec as [P' [Q' [X' has_spec']]].
   rewrite has_spec, has_spec' in safe_over. destruct safe_over as [P'ok [Q'ok X'ok]].
   destruct (SNM.safe_native preclasses privclasses _ _ _ _ _ P' Q' X' r1 (r2 :*: caller_allowance) exec_safe cl_loaded native has_spec' native_eq (P'ok _ P_ok) rem_ok) as [r' [post_cond [r'_ok [pres [only nolimchange]]]]]; auto.
   destruct native_result. destruct resval; simpl in *.
     left. match type of EXEC with JVM.cont ?S = result => exists S end.
     repeat split; auto.
     eapply mk_safe_state; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite <- combine_assoc in r'_ok. apply r'_ok.
     eapply mk_safe_current_frame; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite (combine_symm r2 r'). rewrite <- (combine_assoc r'). reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.

     left. match type of EXEC with JVM.cont ?S = result => exists S end.
     repeat split; auto.
     eapply mk_safe_state; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite <- combine_assoc in r'_ok. apply r'_ok.
     eapply mk_safe_current_frame; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     rewrite (combine_symm r2 r'). rewrite <- (combine_assoc r'). reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto using preserve_constantpool_additional_correct, CP.preserve_old_classes_trans, CP.compose_only_add, preserve_all_classes_verified, preserve_all_preclasses_verified.
     
     eapply throw_exception_prop.
       apply EXEC.
       apply code_verified_copy.
       eapply preserve_constantpool_additional_correct; eauto.
       eauto using CP.preserve_old_classes_trans.
       eauto using CP.compose_only_add.
       apply (leq_refl ((r2:*:r') :*: caller_allowance)). reflexivity.
       apply grants_ok.
       rewrite ensures_spec. eauto using preserve_safe_frame_stack_rest.
       eassumption.
       apply X_ok. apply X'ok. apply post_cond.
       simpl in *. rewrite combine_assoc. rewrite (combine_symm r2 r'). rewrite combine_assoc. rewrite <- combine_assoc. assumption.
       eapply preserve_all_classes_verified; eauto.
       eapply preserve_all_preclasses_verified; eauto.
       simpl. apply nolimchange.

   right; right; right; assumption.
  (* method not found *)
  eapply throw_builtin_exception_ok; eauto.
   eapply preserve_constantpool_additional_correct; eauto.
   rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.
 (* null pointer *)
 eapply throw_builtin_exception_ok; eauto.
  eapply preserve_constantpool_additional_correct; eauto.
  rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.

(* op_aconst_null *)
subst pc0 a2. simpl in EXEC. intuition eauto 7.

(* op_checkcast *)
subst a2 t pc0. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
rewrite H1 in EXEC.

assert (exists classes', exists p : CP.preserve_old_classes classes classes', exists o, exists c, exists H, E.R.resolve_class (C.class_name class) clsnm classes preclasses = CP.load_ok _ p o c H).
 destruct H2.
  destruct (cpa_classref _ _ _ _ _ cpa_ok idx clsnm H1 H) as [classes' [p [oa [c [c_exists resolve_ok]]]]]. intuition eauto 6.
  destruct (cpa_ins_class _ _ _ _ _ cpa_ok idx clsnm H1 H) as [classes' [p [oa [c [c_exists [resolve_ok _]]]]]]. intuition eauto 6.
destruct H as [classes' [p [oa [c [H resolve_ok]]]]].

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

rewrite resolve_ok in EXEC.

destruct this_sat_a. fold sat in *.
destruct o.
 (* nonnull pointer *)
 destruct (RT.heap_lookup_class (RT.preserve_cert_heap heap p) a0) as [[obj_cls_nm X] | _].
  (* object exists *)
  destruct (A.is_assignable classes' (C.ty_obj obj_cls_nm) (C.ty_obj clsnm)).
   (* is assignable *)
   left. eapply ex_intro. repeat split.
    eassumption.
    eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
     eapply preserve_constantpool_additional_correct; eauto.
     eapply preserve_safe_frame_stack_rest; eauto.
     auto.
   (* not assignable: throw exception *)
   eapply throw_builtin_exception_ok with (classes:=classes') (exn:=CP.errClassCast); eauto.
    eapply preserve_constantpool_additional_correct; eauto.
    rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.
  (* object doesn't exist *)
  right. right. right. assumption.
 (* null pointer *)
 left. eapply ex_intro. repeat split.
  eassumption.
  eapply mk_safe_state; eauto. eapply mk_safe_current_frame; eauto.
   eapply preserve_constantpool_additional_correct; eauto.
   eapply preserve_safe_frame_stack_rest; eauto.
  auto.

(* op_getfield *)
subst t pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
rewrite H1 in EXEC.

destruct (cpa_instance_field _ _ _ _ _ cpa_ok idx clsnm fnm ty H1 H2)
      as [classes' [p [oa [c [f [[X1 X2] [resolve_ok [not_static not_final]]]]]]]].
clear H2 H1.

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

destruct this_sat_a. fold sat in *.

rewrite resolve_ok in EXEC.
rewrite not_static in EXEC.
destruct o.
 (* reference is not null *)
 match goal with _:(match ?x with inleft _ => _ | inright _ => _ end) = _ |- _ => destruct x end.
  (* object exists *)
  destruct s.
  left. eapply ex_intro. repeat split.
   eassumption.
   eapply mk_safe_state; eauto.
    eapply mk_safe_current_frame; eauto.
     eapply preserve_constantpool_additional_correct; eauto.
     eapply preserve_safe_frame_stack_rest; eauto.
   auto.
  (* object not there *)
  right. right. right. assumption.
 (* reference is null *)
 eapply throw_builtin_exception_ok with (classes:=classes') (exn:=CP.errNullPointer); eauto.
  eapply preserve_constantpool_additional_correct; eauto.
  rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.

(* op_getstatic *)
subst t pc0 a2. simpl in EXEC.
rewrite H1 in EXEC.

destruct (cpa_static_field _ _ _ _ _ cpa_ok idx clsnm fnm ty H1 H2)
      as [classes' [p [oa [c [f [[X1 X2] [resolve_ok static]]]]]]].
clear H2 H1.

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

rewrite resolve_ok in EXEC.
destruct (BoolExt.bool_informative (C.field_static f)).
 (* field is static *)
 match goal with _:(match ?x with exist _ _ => _ end) = _ |- _ => destruct x end.
 left. eapply ex_intro. repeat split.
  eassumption.
  eapply mk_safe_state; eauto.
   eapply mk_safe_current_frame; eauto.
    eapply preserve_constantpool_additional_correct; eauto.
    eapply preserve_safe_frame_stack_rest; eauto.
  auto.
 (* field not static: impossible *)
 rewrite e0 in static. discriminate.

(* op_new *)
subst t pc0 a2. simpl in EXEC.
rewrite H1 in EXEC.

destruct (cpa_ins_class _ _ _ _ _ cpa_ok idx clsnm H1 H2) as [classes' [p [oa [c [c_exists [resolve_ok [not_interface not_abstract]]]]]]].
clear H2 H1.

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

rewrite resolve_ok in EXEC.
rewrite not_abstract in EXEC.
destruct (BoolExt.bool_informative (C.class_interface c)). 
 (* but it is an interface: impossible *)
 rewrite not_interface in e0. discriminate.
 (* actually create the object *)
 match goal with _:match ?x with Twosig.pack2 _ _ _ => _ end = _ |- _ =>
    destruct x as [heap0 addr [X1 [X2 [X3 [preserved X4]]]]] end.
 left. eapply ex_intro. repeat split.
  eassumption.
  unfold R_tensor in *.
  destruct (r_new clsnm) as [r|] _eqn: new_r.
   destruct (r_new_match _ _ new_r) as [a_r [new_a a_r_eq]].
   rewrite new_a in this_sat_a.
   destruct this_sat_a as [r1 [r2 [r1r2_this [clsnm_r1 r2_a]]]]. fold sat in r2_a.
   eapply mk_safe_state.
    assert (r <: r1) by (eapply leq_trans; [ eapply leq_refl; rewrite <- a_r_eq; reflexivity | apply clsnm_r1 ]).
    rewrite H at 1; try (apply leq_refl; reflexivity).
    rewrite <- combine_assoc.
    eapply leq_trans.
     apply (leq_refl (consumed :*: (r1 :*: (r2 :*: caller_allowance)))). reflexivity.
     rewrite (combine_assoc r1 r2 caller_allowance).
     rewrite r1r2_this; try (apply leq_refl; reflexivity).
     rewrite this_p_caller_leq_current; try (apply leq_refl; reflexivity).
     assumption.
    eapply mk_safe_current_frame; eauto.
     eapply preserve_constantpool_additional_correct; eauto.
     apply leq_refl. reflexivity.
     eapply preserve_safe_frame_stack_rest; eauto.
    eassumption.
    eassumption.
   rewrite (r_new_empty _ new_r) in this_sat_a.
   eapply mk_safe_state.
    eassumption.
    eapply mk_safe_current_frame; eauto.
     eapply preserve_constantpool_additional_correct; eauto.
     eapply preserve_safe_frame_stack_rest; eauto.
    eassumption.
    eassumption.
  auto.

(* op_putfield *)
subst t pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct r0; try (right; right; right; assumption).
rewrite H1 in EXEC.

destruct (cpa_instance_field _ _ _ _ _ cpa_ok idx clsnm fnm ty H1 H2)
      as [classes' [p [oa [c [f [[X1 X2] [resolve_ok [not_static not_final]]]]]]]].
clear H2 H1.

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

destruct this_sat_a. fold sat in *.

rewrite resolve_ok in EXEC.
rewrite not_static in EXEC.
rewrite not_final in EXEC. simpl in EXEC.
destruct o.
 (* reference is not null *)
 match goal with _:match ?x with left _ => _ | right _ => _ end = _ |- _ => destruct x end; try (right; right; right; assumption).
 match goal with _:(match ?x with inleft _ => _ | inright _ => _ end) = _ |- _ => destruct x as [[heap' [Y1 [Y2 Y3]]]|_] end.
  (* object exists *)
  left. eapply ex_intro. repeat split.
   eassumption.
   eapply mk_safe_state; eauto.
    eapply mk_safe_current_frame; eauto.
     eapply preserve_constantpool_additional_correct; eauto.
     eapply preserve_safe_frame_stack_rest; eauto.
    auto.
  (* object not there *)
  right. right. right. assumption.
 (* reference is null *)
 eapply throw_builtin_exception_ok with (classes:=classes') (exn:=CP.errNullPointer); eauto.
  eapply preserve_constantpool_additional_correct; eauto.
  rewrite ensures_spec. eapply preserve_safe_frame_stack_rest; eauto.

(* op_putstatic *)
subst t pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
rewrite H1 in EXEC.

destruct (cpa_static_field _ _ _ _ _ cpa_ok idx clsnm fnm ty H1 H2)
      as [classes' [p [oa [c [f [[X1 X2] [resolve_ok static]]]]]]].
clear H2 H1.

assert (all_preclasses_v':all_preclasses_verified preclasses privclasses classes'). eapply preserve_all_preclasses_verified; eassumption.
assert (all_classes_v':all_classes_verified preclasses privclasses classes'). eapply preserve_all_classes_verified; eassumption.

rewrite resolve_ok in EXEC.
destruct (BoolExt.bool_informative (C.field_static f)).
 (* field is static *)
 match goal with _:match ?x with left _ => _ | right _ => _ end = _ |- _ => destruct x end; try (right; right; right; assumption).
 match goal with _:(match ?x with exist _ _ => _ end) = _ |- _ => destruct x end.
 left. eapply ex_intro. repeat split.
  eassumption.
  eapply mk_safe_state; eauto.
   eapply mk_safe_current_frame; eauto.
    eapply preserve_constantpool_additional_correct; eauto.
    eapply preserve_safe_frame_stack_rest; eauto.
   auto.
 (* field not static: impossible *)
 rewrite e0 in static. discriminate.

(* op_if_acmp *)
subst a z pc0 a2. simpl in EXEC. 
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).

destruct this_sat_a. fold sat in *.

destruct op.
 destruct (E.option_addr_eq_dec o o0); [rewrite H1 in EXEC|]; intuition eauto 7.
 destruct (E.option_addr_eq_dec o o0); [|rewrite H1 in EXEC]; intuition eauto 7.

(* op_if_icmp *)
subst c z pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).

destruct this_sat_a. fold sat in *.

destruct op;
(match goal with _:match (if ?x then _ else _) with Some _ => _ | None => _ end = _ |- _ => destruct x end;
[rewrite H1 in EXEC|]; intuition eauto 7).

(* op_if *)
subst c z pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).

destruct this_sat_a. fold sat in *.

destruct op;
(match goal with _:match (if ?x then _ else _) with Some _ => _ | None => _ end = _ |- _ => destruct x end;
[rewrite H1 in EXEC|]; intuition eauto 7).

(* op_ifnonnull *)
subst z pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).

destruct this_sat_a. fold sat in *.

destruct o; [rewrite H0 in EXEC|]; intuition eauto 7.

(* op_ifnull *)
subst z pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).

destruct this_sat_a. fold sat in *.

rewrite H0 in EXEC.
destruct o; intuition eauto 7.

(* op_goto *)
subst z pc0 a2. simpl in EXEC.

rewrite H0 in EXEC. intuition eauto 7.

(* op_valreturn *)
subst s pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
set (new_reslimit := E.update_reslimit privclasses class method total_allowance).
assert (uplimit : E.update_reslimit privclasses class method total_allowance = new_reslimit) by reflexivity.
clearbody new_reslimit.
destruct (update_reslimit_ok _ _ _ _ _ _ uplimit grants_ok this_sat_a) as [r' [update_cond [update_sat update_incr]]].

destruct fs.
 (* fell off the top of the stack *)
 right. left. eapply ex_intro. eapply ex_intro. repeat split.
  eassumption.
  rewrite uplimit. destruct update_cond.
   rewrite H. apply no_allowance_change; auto.
   apply priv_allowance_change; auto.
  simpl. rewrite <- (r_combine_e consumed). rewrite (e_bottom current_allowance); try (apply leq_refl; reflexivity). rewrite uplimit. eapply leq_trans. apply leq_total_allowance. rewrite <- (r_combine_e total_allowance). apply leq_trans with (r2:=total_allowance :*: r'). apply combine_order. apply leq_refl. reflexivity. apply e_bottom. assumption.
 (* another frame *)
 destruct f. left. eapply ex_intro. repeat split.
  eassumption.
  eapply mk_safe_state; eauto.
   rewrite uplimit. instantiate (1:=current_allowance:*:r'). eapply leq_trans. rewrite combine_assoc at 1. apply combine_order. apply leq_total_allowance. apply leq_refl. reflexivity. assumption.
   inversion fs_safe. subst. eapply mk_safe_current_frame.
    apply H7.
    apply H8.
    apply H9.
    apply H14. apply update_sat.
    rewrite (combine_symm this_allowance0 (this_allowance:*:r')) at 1. rewrite <- combine_assoc. instantiate (1:=caller_allowance0). rewrite <- combine_assoc. rewrite (combine_symm r'). rewrite combine_assoc. apply combine_order. eapply leq_trans.
     eapply combine_order.
      apply leq_refl. reflexivity.
      apply H16.
     assumption.
     apply leq_refl. reflexivity.
    assumption.
    reflexivity. assumption.
  rewrite uplimit. destruct update_cond.
   rewrite H. apply no_allowance_change; auto.
   apply priv_allowance_change; auto.


(* op_return *)
subst pc0 a2. simpl in EXEC.
set (new_reslimit := E.update_reslimit privclasses class method total_allowance).
assert (uplimit : E.update_reslimit privclasses class method total_allowance = new_reslimit) by reflexivity.
clearbody new_reslimit.
destruct (update_reslimit_ok _ _ _ _ _ _ uplimit grants_ok this_sat_a) as [r' [update_cond [update_sat update_incr]]].

destruct fs.
 (* fell off the top of the stack *)
 right. left. eapply ex_intro. eapply ex_intro. repeat split.
  eassumption.
  rewrite uplimit. destruct update_cond.
   rewrite H. apply no_allowance_change; auto.
   apply priv_allowance_change; auto.
  simpl. rewrite <- (r_combine_e consumed). rewrite (e_bottom current_allowance); try (apply leq_refl; reflexivity).  rewrite uplimit. eapply leq_trans. apply leq_total_allowance. rewrite <- (r_combine_e total_allowance). apply leq_trans with (r2:=total_allowance :*: r'). apply combine_order. apply leq_refl. reflexivity. apply e_bottom. assumption.
 (* another frame *)
 destruct f. left. eapply ex_intro. repeat split.
  eassumption.
  eapply mk_safe_state; eauto.
    rewrite uplimit. instantiate (1:=current_allowance:*:r'). eapply leq_trans. rewrite combine_assoc at 1. apply combine_order. apply leq_total_allowance. apply leq_refl. reflexivity. assumption.
   inversion fs_safe. subst. eapply mk_safe_current_frame.
    apply H7.
    apply H8.
    apply H9.
    apply H14. eassumption.
    rewrite (combine_symm this_allowance0 (this_allowance:*:r')) at 1. rewrite <- combine_assoc. instantiate (1:=caller_allowance0). rewrite <- combine_assoc. rewrite (combine_symm r'). rewrite combine_assoc. apply combine_order. eapply leq_trans.
     eapply combine_order.
      apply leq_refl. reflexivity.
      apply H16.
     assumption.
     apply leq_refl. reflexivity.
    assumption.
    reflexivity. assumption.
  rewrite uplimit. destruct update_cond.
   rewrite H. apply no_allowance_change; auto.
   apply priv_allowance_change; auto.

(* op_athrow *)
subst pc0 a2. simpl in EXEC.
destruct stk; try (right; right; right; assumption).
destruct r; try (right; right; right; assumption).

destruct this_sat_a. fold sat in *.

destruct o.
 (* throwing an actual exception *)
 destruct (RT.heap_lookup_class heap a0) as [[cls_nm _] | _]; try (right; right; right; assumption).
 destruct (A.is_assignable classes (C.ty_obj cls_nm) (C.ty_obj B.java_lang_Throwable)); try (right; right; right; assumption).
 eapply throw_exception_prop; eauto.
  rewrite ensures_spec. assumption.
 (* throwing null pointer exception *)
 eapply throw_builtin_exception_ok; eauto.
  rewrite ensures_spec. assumption.

(* op_iconst *)
subst t pc0 a2. simpl in EXEC. intuition eauto 7.
Save.

End WithPreclasses.


(** * Show that we can construct an initial safe state. *)

(** First we need to know that the initial classpool (containing only
    java.lang.Object) is verified. *)

Module BIC := BuiltinClasses.BuiltinClasses B ANN.GA.A C CP.

Lemma initial_ok : forall preclasses priv, all_classes_verified preclasses priv BIC.initial_classes.
Proof.
econstructor; destruct (CP.initial_has_jlo _ _ _ _ _ H); subst cnm class.
  instantiate (1:=ANN.ConstantPoolAdditional.empty).
  (* If we imported the checker we could use it (as in the commented out proof
     script below, but instead we just use the fact that the constant pool is
     empty. *)
  simpl in *. unfold BIC.j_l_Object_pool.
  constructor; intros; rewrite C.ConstantPool.lookup_empty in H1; discriminate.
(*
  apply check_constantpool_additional_ok.
  unfold check_constantpool_additional.  rewrite RC_ANN.ConstantPoolAdditional.elements_empty.
  reflexivity.
*)
  intros md m lookup.
  simpl in lookup. unfold BIC.j_l_Object_methods in *.
  left. exists (C.mkCode 0 1 (C.op_return :: nil) nil).
  intros P Q X has_spec.
  destruct (C.MethodList.Key.eq_dec (B.init, C.mkDescriptor None nil) md) as [isinit|isinit]; unfold C.MethodList.Key.eq in isinit.
    subst md.
    rewrite C.MethodList.lookup_update in lookup. injection lookup as meq. subst m.
    exists (CERT.Cert.update CERT.Cert.empty 0 Q). exists P. exists Q.
    cbv in has_spec; injection has_spec; intros xx qq pp; subst X Q P.
    split.
      reflexivity.
    split.
      right; split; reflexivity.
    split.
      constructor. intros. destruct n. auto.
      rewrite CERT.Cert.indep_lookup in H1; auto. rewrite CERT.Cert.lookup_empty in H1. discriminate.

      intros n op oplookup. destruct n.
        apply mk_verified_instruction with (a1:=f_i) (a2:=f_i).
        apply CERT.Cert.lookup_update.
        simpl in oplookup. injection oplookup as opeq. subst op.
        apply v_return.
        apply SYN.implies_refl.

        destruct n; simpl in oplookup; discriminate.

    rewrite CERT.Cert.lookup_update. tauto.

    rewrite C.MethodList.indep_lookup in lookup; auto. rewrite C.MethodList.lookup_empty in lookup. discriminate.

  intros until mB. intros notinit _ _ _ _ lookup _ _ _.
  destruct (C.MethodList.Key.eq_dec (B.init, C.mkDescriptor None nil) md) as [isinit|isinit]; unfold C.MethodList.Key.eq in isinit.
    subst md. simpl in notinit. tauto.
    simpl in lookup.  unfold BIC.j_l_Object_methods in *. rewrite C.MethodList.indep_lookup in lookup. rewrite C.MethodList.lookup_empty in lookup. discriminate.
      unfold C.MethodList.Key.eq. assumption.

  intros until mB. intros _ _ Iloaded _ Iinterface.
  destruct (CP.initial_has_jlo _ _ _ _ _ Iloaded). subst cI.
  simpl in Iinterface. discriminate.
Qed.

(** Now we can show that starting the virtual machine on any suitable static
    method with enough resources to satisfy the method's precondition puts us
    into a safe state. *)

Theorem initial_state_is_safe : forall preclasses privclasses classname methname descriptor args r method classes' preserve onlypreclasses c cloaded methodloaded cassignable code result,
  all_preclasses_verified preclasses privclasses BIC.initial_classes ->
  R.resolve_method classname classname methname descriptor BIC.initial_classes preclasses = CP.load_ok (classes':=classes') _ preserve onlypreclasses (c,method) (conj cloaded (conj methodloaded cassignable)) ->
  C.class_interface c = false ->
  C.method_static method = true ->
  C.method_code method = Some code ->
  BASESEM.sat r (fst (fst (method_spec method))) ->
  let s := RT.mkState nil BIC.initial_classes (RT.empty_heap BIC.initial_classes) (RT.empty_fieldstore BIC.initial_classes (RT.empty_heap BIC.initial_classes)) RA.e r in
  E.init preclasses classname methname descriptor args s = result ->
  safe_result preclasses privclasses s result.
Proof.
  unfold safe_result.
  intros until result. intros preclasses_ok resolves notiface isstatic hascode r_ok init_result.
  assert (classes'_ok : all_classes_verified preclasses privclasses classes') by
    (apply preserve_all_classes_verified with (classes:=BIC.initial_classes); auto using initial_ok).
  destruct (classes'_ok (C.class_name c) c); auto.
  case_eq (method_spec method). intros [P Q] X spec. rewrite spec in r_ok.
  simpl in *. rewrite resolves in init_result.
  rewrite hascode in init_result.
  rewrite isstatic in init_result.
  destruct (E.stack_to_lvars args (C.code_max_lvars code)).
    simpl in *.
    destruct (class_verified_methods (methname,descriptor) method methodloaded) as [[code' code_ok]|[nocode abs_or_nat]].
      destruct (code_ok P Q X spec) as [cert [P' [Q' [code_eq [grantsok [verified [resok certok]]]]]]]; auto.
      rewrite hascode in code_eq. injection code_eq as code_eq'. subst code'.
      left. match type of init_result with context [JVM.cont ?s' = result] => exists s' end. (repeat split); auto.
        econstructor;auto. apply leq_refl. apply e_combine_r. econstructor; eauto. apply leq_refl; apply r_combine_e. apply safe_stack_nil.
        apply preserve_all_preclasses_verified with (classes:=BIC.initial_classes); auto.
      apply no_allowance_change. reflexivity.

      rewrite hascode in nocode. discriminate.

    tauto.
Qed.

End ResourceSafety.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

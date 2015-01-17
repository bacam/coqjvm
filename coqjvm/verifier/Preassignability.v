Require Import BasicMachineTypes.
Require Import ClasspoolIface.
Require Import ClassDatatypesIface.
Require Import AssignabilityIface.
Require Import PreassignabilityIface.
Require Import VirtualMethodLookupIface.
Require Import GenericAnnotationIface.
Require Import List.

Require Import AnnotationIface.

(* coq 8.2 rewrite workaround, see https://logical.saclay.inria.fr/coq-bugs/show_bug.cgi?id=1938 *)

Ltac frewrite t :=
let Hnew := fresh in
    assert (Hnew := t);
    rewrite Hnew in *;
    clear Hnew.

Module MkPreassignability (B  : BASICS)
                          (GA : GENERIC_ANNOTATION B)
                          (C  : CLASSDATATYPES B GA.A)
                          (CP : CLASSPOOL B GA.A C)
                          (A : ASSIGNABILITY B GA.A C CP)
                          (VM : VIRTUALMETHODLOOKUP B GA.A C CP A)
                     : PREASSIGNABILITY B GA C CP A VM.

Inductive pc_sub_class (classes:CP.cert_classpool) (preclasses:CP.Preclasspool.t) : B.Classname.t -> B.Classname.t -> Prop :=
| pc_sub_class_refl : forall c cl,
    CP.Preclasspool.lookup preclasses c = Some cl ->
    (forall cl', ~ CP.class_loaded classes c cl') ->
    pc_sub_class classes preclasses c c
| pc_sub_class_step : forall c c' c'' cl,
    CP.Preclasspool.lookup preclasses c  = Some cl  ->
    (forall cl', ~ CP.class_loaded classes c cl') ->
    cl.(C.preclass_super_name) = Some c' ->
    pc_sub_class classes preclasses c' c'' ->
    pc_sub_class classes preclasses c c''.

Inductive pc_cross_sub_class (classes:CP.cert_classpool) (preclasses:CP.Preclasspool.t) : B.Classname.t -> B.Classname.t -> Prop :=
| pc_cross_sub_class_cross : forall c c' c'' cl,
    CP.Preclasspool.lookup preclasses c  = Some cl  ->
    (forall cl', ~ CP.class_loaded classes c cl') ->
    cl.(C.preclass_super_name) = Some c' ->
    A.sub_class classes c' c'' ->
    pc_cross_sub_class classes preclasses c c''
| pc_cross_sub_class_step : forall c c' c'' cl,
    CP.Preclasspool.lookup preclasses c  = Some cl  ->
    (forall cl', ~ CP.class_loaded classes c cl') ->
    cl.(C.preclass_super_name) = Some c' ->
    pc_cross_sub_class classes preclasses c' c'' ->
    pc_cross_sub_class classes preclasses c c''.


Lemma subs_not_loaded : forall classes classes' nm nm_t,
  (forall c, ~CP.class_loaded classes nm_t c) ->
  A.sub_class classes' nm nm_t ->
  CP.preserve_old_classes classes classes' ->
  (forall c, ~CP.class_loaded classes nm c).
Proof.
  (* To show that nm isn't loaded before we have to
     crawl our way back up to nm_t, which we know wasn't loaded. *)
  intros classes classes' nm nm_t notloaded_t subclass preserve.
  induction subclass as [nm_t cl_t nm_t_loaded|nm1 nm_t nm2 cl1 loaded1 super1 subclass'']; intros s_cl s_loaded.
    destruct (notloaded_t s_cl s_loaded).
            
    assert (cl1 = s_cl).
      apply (preserve nm1) in s_loaded.
      apply (CP.class_loaded_unique (c2:=s_cl) loaded1) in s_loaded.
      assumption.
    subst cl1.
    destruct (CP.class_super_loaded classes _ _ _ s_loaded super1) as [cl2 loaded2].
    apply IHsubclass'' with (c:=cl2); assumption.
Qed.

Lemma rev_preserve_sub_class : forall classes classes' nmA nmB clA,
  CP.preserve_old_classes classes classes' ->
  A.sub_class classes' nmA nmB ->
  CP.class_loaded classes nmA clA ->
  A.sub_class classes nmA nmB.
Proof.
  intros classes classes' nmA nmB clA preserve subclass.
  generalize clA.
  clear clA.
  induction subclass as [nm1 cl1 loaded1|nm1 nmB nm2 cl1 loaded1 super1 subclass1];
  intros cl' loaded'.
    eauto using A.sub_class_refl.

    assert (cl'=cl1).
      apply (preserve nm1) in loaded'.
      apply (CP.class_loaded_unique (c2:=cl1) loaded') in loaded1.
      assumption.
    subst cl'.
    apply A.sub_class_step with (c:=cl1) (s_nm:=nm2); auto.
    destruct (CP.class_super_loaded _ _ _ _ loaded' super1) as [cl2 loaded2].
    eapply IHsubclass1; eauto.
Qed.

Lemma pc_loaded_cross_super_class : forall classes classes' preclasses nm nmB,
  (forall c, ~CP.class_loaded classes nmB c) ->
  pc_cross_sub_class classes' preclasses nm nmB ->
  CP.preserve_old_classes classes classes' ->
  CP.only_add_from_preclasses classes classes' preclasses ->
  pc_sub_class classes preclasses nm nmB.
Proof.
  intros until nmB.
  intros notloaded cross preserve add.
  induction cross as [c c' c'' cl lookup_c notloaded_c super_c subclass|].
    eapply pc_sub_class_step; eauto.
      intros cl' cl'loaded.
      apply (notloaded_c cl').
      apply preserve.
      apply cl'loaded.

      clear super_c.
      induction subclass as [nm c' nmloaded|nm nm_t s_nm c' nmloaded c_is_s_nm subclass'].
        destruct (add nm c' nmloaded) as [[nm_pc [_ [nm_lookup _]]]|].
          eapply pc_sub_class_refl.
            apply nm_lookup.

            assumption.

            destruct (notloaded c' H).

        destruct (add nm c' nmloaded) as [[pc' [pcc [nmlookup nmnotloaded]]]|nmloaded'].
          eapply pc_sub_class_step.
            apply nmlookup.

            assumption.

            destruct (CP.preclass_to_class_props _ _ pcc) as [_ [_ [_ [_ [H _]]]]].
            rewrite <- H.
            apply c_is_s_nm.

            apply IHsubclass'.
              assumption.

          destruct (CP.class_super_loaded _ _ _ _ nmloaded' c_is_s_nm) as [s_cl s_loaded].
          absurd (CP.class_loaded classes s_nm s_cl); [|assumption].
          apply subs_not_loaded with (classes':=classes') (nm_t:=nm_t);
          auto.

    apply pc_sub_class_step with (cl:=cl) (c':=c'); auto.
      intros cl' cl'_in_classes.
      apply (preserve c cl') in cl'_in_classes.
      exact (H0 cl' cl'_in_classes).
Qed.

Lemma pc_preserve_sub_class : forall classes classes' preclasses nmA nmB,
  pc_sub_class classes' preclasses nmA nmB ->
  (forall c, ~CP.class_loaded classes' nmB c) ->
  CP.preserve_old_classes classes classes' ->
  CP.only_add_from_preclasses classes classes' preclasses ->
  pc_sub_class classes preclasses nmA nmB.
Proof.
  intros until nmB.
  intros subclass notloadedB preserve onlyadd.
  induction subclass as [nm cl|nmA nm' nmB clA lookupA notloadedA superA subclass'].
    apply pc_sub_class_refl with (cl:=cl); auto.
      intros cl' loaded'.
      apply (preserve nm cl') in loaded'.
      exact (notloadedB cl' loaded').

    apply pc_sub_class_step with (cl:=clA) (c':=nm'); auto.
      intros cl' loaded'.
      apply (preserve nmA cl') in loaded'.
      exact (notloadedA cl' loaded').
Qed.

Lemma pc_loaded_sub_class : forall classes classes' preclasses nmA nmB,
  A.sub_class classes' nmA nmB ->
  (forall c, ~CP.class_loaded classes nmA c) ->
  (forall c, ~CP.class_loaded classes nmB c) ->
  CP.preserve_old_classes classes classes' ->
  CP.only_add_from_preclasses classes classes' preclasses ->
  pc_sub_class classes preclasses nmA nmB.
Proof.
  intros until nmB.
  intros subclass notloadedA notloadedB preserve onlyadd.
  induction subclass as [nm cl loaded|nmA nmB nm' clA loadedA superA subclass'].
    destruct (onlyadd nm cl loaded) as [[pc [pcc [nmlookup nmnotloaded]]]|nmloaded].
      apply pc_sub_class_refl with (cl:=pc); assumption.
    
      destruct (notloadedA cl nmloaded).

    destruct (onlyadd nmA clA loadedA) as [[pcA [pccA [nmlookupA nmnotloadedA]]]|nmloadedA].
      destruct (CP.preclass_to_class_props pcA clA pccA) as [_ [_ [_ [_ [supername _]]]]].
      apply pc_sub_class_step with (cl:=pcA) (c':=nm'); auto.
        rewrite <- supername.
        assumption.

        apply IHsubclass'; eauto using subs_not_loaded.

      destruct (notloadedA clA nmloadedA).
Qed.

Lemma pc_loaded_cross_sub_class : forall classes classes' preclasses nmA nmB cB,
  A.sub_class classes' nmA nmB ->
  (forall c, ~CP.class_loaded classes nmA c) ->
  CP.class_loaded classes nmB cB ->
  CP.preserve_old_classes classes classes' ->
  CP.only_add_from_preclasses classes classes' preclasses ->
  pc_cross_sub_class classes preclasses nmA nmB.
Proof.
  intros until cB.
  intros subclass notloadedA loadedB preserve onlyadd.
  destruct subclass as [nm cl loaded|nmA nmB nm' clA loadedA superA subclass].
    destruct (notloadedA cB loadedB).

    destruct (onlyadd nmA clA loadedA) as [[pcA [pccA [nmlookupA _]]]|nmloadedA];
    [|destruct (notloadedA clA nmloadedA)].
    destruct (CP.preclass_to_class_props _ _ pccA) as [_ [_ [_ [_ [super' _]]]]].
    generalize nmA clA loadedA superA notloadedA pcA pccA nmlookupA super'.
    clear nmA clA loadedA superA notloadedA pcA pccA nmlookupA super'.
    induction subclass as [nm cl loaded|nm nmB nm' cl loaded super subclass'];
    intros nmA clA loadedA superA notloadedA pcA pccA nmlookupA super'.
      apply pc_cross_sub_class_cross with (cl:=pcA) (c':=nm); auto.
        rewrite <- super'.
        apply superA.

        apply A.sub_class_refl with (cwitness:=cB).
        assumption.

      destruct (onlyadd nm cl loaded) as [[pc [pcc [nmlookup nmnotloaded]]]|nmloaded].
        apply pc_cross_sub_class_step with (cl:=pcA) (c':=nm); auto.
          rewrite <- super'.
          apply superA.

          destruct (CP.preclass_to_class_props _ _ pcc) as [_ [_ [_ [_ [super'' _]]]]].
          eapply IHsubclass'; eauto.

        apply pc_cross_sub_class_cross with (cl:=pcA) (c':=nm); auto.
          rewrite <- super'.
          apply superA.

          apply A.sub_class_step with (c:=cl) (s_nm:=nm'); auto.
          destruct (CP.class_super_loaded _ _ _ _ nmloaded super) as [cl' loaded'].
          eapply rev_preserve_sub_class with (classes':=classes'); eauto.
Qed.
          
Lemma pc_preserve_cross_sub_class : forall classes classes' preclasses nmA nmB c,
  CP.class_loaded classes nmB c ->
  pc_cross_sub_class classes' preclasses nmA nmB ->
  CP.preserve_old_classes classes classes' ->
  CP.only_add_from_preclasses classes classes' preclasses ->
  pc_cross_sub_class classes preclasses nmA nmB.
Proof.
  intros until c.
  intros loaded_nmB cross_AB' preserve onlyadd.

  induction cross_AB' as [nm1 nm2 nm3 pc1 lookup1 notloaded1 super1 subclass|nm1 nm2 nm3 cl1 lookup1 notloaded1 super1 subclass].
    destruct (CP.class_loaded_dec classes nm2) as [[cl2 loaded2]|notloaded2].
      apply pc_cross_sub_class_cross with (cl:=pc1) (c':=nm2); auto.
        intros cl' loaded1.
        apply (preserve nm1) in loaded1.
        destruct (notloaded1 cl' loaded1).

        eapply rev_preserve_sub_class; eauto.

      eapply pc_cross_sub_class_step; eauto.
        intros cl' loaded1.
        apply (preserve nm1) in loaded1.
        destruct (notloaded1 cl' loaded1).

        eapply pc_loaded_cross_sub_class; eauto.

    eapply pc_cross_sub_class_step; eauto.
      intros cl' loaded1.
      apply (preserve nm1) in loaded1.
      destruct (notloaded1 cl' loaded1).
Qed.



Lemma pre_assignable_barrier : forall classes preclasses nmA nmS pcA nmS' cS' pcS,
 pc_sub_class classes preclasses nmA nmS ->
 CP.Preclasspool.lookup preclasses nmA = Some pcA ->
 CP.Preclasspool.lookup preclasses nmS = Some pcS ->
 C.preclass_super_name pcA = Some nmS' ->
 C.preclass_interface pcS = false ->
 CP.class_loaded classes nmS' cS' ->
 nmA = nmS.
Proof.
  intros until pcS.
  intros subclass lookupA lookupS superA intS loadedS'.
  destruct subclass as [|nmA nmS'' nmS pcA' lookupA' notloadedA superA' subclass'].
    reflexivity.

    rewrite lookupA in lookupA'.
    injection lookupA' as pcA'eq.
    subst pcA'.
    rewrite superA' in superA.
    injection superA as nmS'eq.
    subst nmS''.
    inversion subclass'; subst; destruct (H0 cS' loadedS').
Qed.  

Lemma pre_assignable_undo_step : forall classes preclasses nm nmS nmS' pc pcS,
 pc_sub_class classes preclasses nm nmS ->
 CP.Preclasspool.lookup preclasses nm = Some pc ->
 CP.Preclasspool.lookup preclasses nmS = Some pcS ->
 C.preclass_super_name pc = Some nmS' ->
 C.preclass_interface pcS = false ->
 nm <> nmS ->
 pc_sub_class classes preclasses nmS' nmS.
Proof.
  intros until pcS.
  intros subclass lookup lookupS super notintS noteq.
  destruct subclass as [|nm nm2 nmS pc' lookup' notloaded super' subclass'].
    destruct noteq.
    reflexivity.

    rewrite lookup in lookup'.
    injection lookup' as pceq.
    subst pc'.
    rewrite super in super'.
    injection super' as nm2eq.
    subst nm2.
    assumption.
Qed.

Lemma cross_assignable_undo_step : forall classes preclasses nm nmS nmS' pc,
 pc_cross_sub_class classes preclasses nm nmS ->
 CP.Preclasspool.lookup preclasses nm = Some pc ->
 C.preclass_super_name pc = Some nmS' ->
 (forall c, ~CP.class_loaded classes nmS' c) ->
 pc_cross_sub_class classes preclasses nmS' nmS.
Proof.
  intros until pc.
  intros subclass lookup super notloadedS.
  destruct subclass as [nm nm2 nmS pc' lookup' notloaded super' subclass'|nm nm2 nmS pc' lookup' notloaded super' subclass'];
  rewrite lookup in lookup';
  injection lookup' as pceq;
  subst pc';
  rewrite super in super';
  injection super' as nmeq;
  subst nm2.
    destruct subclass' as [nmS' witness loaded|nmS' nm_t s_nm witness loaded];
    destruct (notloadedS witness loaded).

    assumption.
Qed.

Lemma top_is_nice : forall classes nm nm_t c,
  A.sub_class classes nm nm_t ->
  CP.class_loaded classes nm c ->
  C.class_interface c = false ->
  exists c_t, CP.class_loaded classes nm_t c_t /\ C.class_interface c_t = false.
Proof.
  intros classes nm nm_t c subclass loaded notint.
  generalize c loaded notint.
  clear c loaded notint.
  induction subclass as [nm c' loaded'|nm nm_t nm' c' loaded' super];
  intros c loaded notint.
    exists c.
    auto.

    pose (scc:=CP.cert_classpool_gives_scc loaded notint).
    clearbody scc.
    apply (CP.class_loaded_unique (c2:=c') loaded) in loaded'.
    subst c'.
    inversion scc as [nosuper|nm0 c0 loaded0 notint0 scc0 supereq].
      rewrite super in nosuper.
      discriminate.

      rewrite super in supereq.
      injection supereq as supereq'.
      subst nm0.
      apply IHsubclass with (c:=c0); auto.
Qed.

Lemma cross_assignable_undo_step_2 : forall classes preclasses nm nmS pc nmS' c,
 pc_cross_sub_class classes preclasses nm nmS ->
 CP.Preclasspool.lookup preclasses nm = Some pc ->
 C.preclass_super_name pc = Some nmS' ->
 CP.class_loaded classes nmS' c ->
 A.assignable classes (C.ty_obj nmS') (C.ty_obj nmS).
Proof.
  intros until c.
  intros subclass lookup super loadedS'.
  destruct subclass as [nm nm2 nmS pc' lookup' notloaded super' subclass'|nm nm2 nmS pc' lookup' notloaded super' subclass'];
  rewrite lookup in lookup';
  injection lookup' as pceq;
  subst pc';
  rewrite super in super';
  injection super' as nmeq;
  subst nm2;
    case_eq (C.class_interface c); intro int.
      destruct subclass' as [nmS c' loaded|nmS' nmS nmM c' loaded super' subclass'].
        apply A.assignable_interface_interface_refl with (cS:=c); auto.

        apply (CP.class_loaded_unique (c2:=c') loadedS') in loaded.
        subst c'.
        rewrite (CP.cert_classpool_gives_interface_super_class_Object loadedS' int) in super'.
        injection super' as nmMeq.
        subst nmM.
        inversion subclass'; subst.
          apply A.assignable_interface_class with (cS:=c); auto.

          destruct (CP.cert_classpool_has_Object classes) as [cO [loadedO [superO [intsO intO]]]].
          rewrite (CP.class_loaded_unique H loadedO) in *.
          rewrite superO in *.
          discriminate.

      pose (scc:=CP.cert_classpool_gives_scc loadedS' int).
      clearbody scc.
      inversion scc as [nosuper|nmA clA loaded notint scc' superA].
        apply sym_eq in nosuper.
        frewrite (CP.no_super_is_jlObject _ _ _ loadedS' nosuper).
        inversion subclass'; subst.
          apply A.assignable_class_class with (cS:=c) (cT:=c); auto.

          rewrite (CP.class_loaded_unique H loadedS') in *.
          rewrite H0 in nosuper.
          discriminate.

        destruct (top_is_nice _ _ _ _ subclass' loadedS' int) as [clS [loadedS notintS]].
        apply A.assignable_class_class with (cS:=c) (cT:=clS); auto.

    inversion subclass'; destruct (H0 c loadedS').
    inversion subclass'; destruct (H0 c loadedS').
Qed.

Section WithClasses.

Variable classes:CP.cert_classpool.
Variable preclasses:CP.Preclasspool.t.

Inductive interface_reqs_method (iface : B.Classname.t) : (B.Methodname.t * C.descriptor) -> GA.method_specification -> Prop :=
| interface_reqs_method_cls : forall c mkey md,
    CP.class_loaded classes iface c ->
    C.MethodList.lookup (C.class_methods c) mkey = Some md ->
    interface_reqs_method iface mkey (GA.method_spec (C.method_annot md))
| interface_reqs_method_precls : forall pc mth,
    (forall c, ~CP.class_loaded classes iface c) ->
    CP.Preclasspool.lookup preclasses iface = Some pc ->
    C.has_premethod (C.preclass_methods pc) (C.premethod_name mth, C.premethod_descriptor mth) mth ->
    interface_reqs_method iface (C.premethod_name mth, C.premethod_descriptor mth) (GA.method_spec (C.premethod_annot mth))
| interface_reqs_method_upcls : forall c iface' mth annot,
    CP.class_loaded classes iface c ->
    In iface' (C.class_interfaces c) ->
    interface_reqs_method iface' mth annot ->
    interface_reqs_method iface mth annot
| interface_reqs_method_upprecls : forall pc iface' mth annot,
    (forall c, ~CP.class_loaded classes iface c) ->
    CP.Preclasspool.lookup preclasses iface = Some pc ->
    In iface' (C.preclass_super_interfaces pc) ->
    interface_reqs_method iface' mth annot ->
    interface_reqs_method iface mth annot.

Inductive minimal_methodspec (nm:B.Classname.t) (md:B.Methodname.t*C.descriptor) (mspec:GA.method_specification) : Prop :=
  | minimal_methodspec_pre : forall pc m,
    (forall c, ~CP.class_loaded classes nm c) ->
    CP.Preclasspool.lookup preclasses nm = Some pc ->
    C.preclass_interface pc = false ->
    C.has_premethod (C.preclass_methods pc) md m ->
    GA.method_spec (C.premethod_annot m) = mspec ->
    C.premethod_static m = false ->
    minimal_methodspec nm md mspec
  | minimal_methodspec_loaded : forall c nmS cS m,
    CP.class_loaded classes nm c ->
    C.class_interface c = false ->
    A.sub_class classes nm nmS ->
    VM.lookup_minimal classes nm nmS md ->
    CP.class_loaded classes nmS cS ->
    C.class_interface cS = false ->
    C.MethodList.lookup (C.class_methods cS) md = Some m ->
    GA.method_spec (C.method_annot m) = mspec ->
    C.method_static m = false ->
    minimal_methodspec nm md mspec
  | minimal_methodspec_prestep : forall pc nmS,
    (forall c, ~CP.class_loaded classes nm c) ->
    CP.Preclasspool.lookup preclasses nm = Some pc ->
    (forall m', C.has_premethod (C.preclass_methods pc) md m' -> C.premethod_static m' = true) ->
    C.preclass_super_name pc = Some nmS ->
    C.preclass_interface pc = false ->
    minimal_methodspec nmS md mspec ->
    minimal_methodspec nm md mspec.

Inductive should_implement : B.Classname.t -> B.Classname.t -> Prop :=
| should_implement_loaded : forall nmA nmB cA cB iface,
  CP.class_loaded classes nmA cA ->
  CP.class_loaded classes nmB cB ->
  C.class_interface cB = false ->
  A.sub_class classes nmA nmB ->
  In iface (C.class_interfaces cB) ->
  should_implement nmA iface
| should_implement_cross : forall nmA nmB cB iface,
  CP.class_loaded classes nmB cB ->
  C.class_interface cB = false ->
  pc_cross_sub_class classes preclasses nmA nmB ->
  In iface (C.class_interfaces cB) ->
  should_implement nmA iface
| should_implement_pre : forall nmA nmB pcB iface,
  (forall c, ~CP.class_loaded classes nmB c) ->
  CP.Preclasspool.lookup preclasses nmB = Some pcB ->
  C.preclass_interface pcB = false ->
  pc_sub_class classes preclasses nmA nmB ->
  In iface (C.preclass_super_interfaces pcB) ->
  should_implement nmA iface.

Lemma does_not_implement : forall nm pc nmS iface,
  CP.Preclasspool.lookup preclasses nm = Some pc ->
  (forall c, ~CP.class_loaded classes nm c) ->
  should_implement nm iface ->
  ~In iface (C.preclass_super_interfaces pc) ->
  C.preclass_super_name pc = Some nmS ->
  should_implement nmS iface.
Proof.
  intros.
  inversion H1.
    destruct (H0 cA H4).

    inversion H6.
      subst.
      rewrite H in H10. injection H10 as pceq.  subst cl.
      rewrite H3 in H12. injection H12 as nmSeq. subst c'.
      assert (l:exists cS, CP.class_loaded classes nmS cS).
        inversion H13; eauto.
      destruct l.
      eapply should_implement_loaded with (nmB:=nmB); eauto.

      rewrite H in H10. injection H10 as pceq.
      subst.
      rewrite H3 in H12. injection H12 as nmSeq. subst c'.
      eapply should_implement_cross with (nmB:=nmB); eauto.

    inversion H7.
      subst.
      rewrite H in H5. injection H5 as pceq. subst pcB.
      contradiction.
      
      subst.
      rewrite H in H11. injection H11 as pceq. subst cl.
      rewrite H3 in H13. injection H13 as nmSeq. subst c'.
      eapply should_implement_pre with (nmB:=nmB); eauto.
Qed.

End WithClasses.

Lemma interface_reqs_preserved : forall classes classes' preclasses iface md annot,
  CP.preserve_old_classes classes classes' ->
  CP.only_add_from_preclasses classes classes' preclasses ->
 (interface_reqs_method classes preclasses iface md annot <->
  interface_reqs_method classes' preclasses iface md annot).
Proof.
  intros until annot.
  intros preserve onlyadd.
  split.

  intro old.
  induction old.
    apply (preserve iface c) in H.
    eapply interface_reqs_method_cls; eauto.

    destruct (CP.class_loaded_dec classes' iface) as [[c loaded']|not_loaded].
      destruct (onlyadd iface c) as [[pc' [convert [lookup' not_before]]]|loaded]; eauto.
        destruct (CP.preclass_to_class_props _ _ convert) as [_ [_ [methods _]]]. 
        destruct (methods (C.premethod_name mth, C.premethod_descriptor mth) (CP.premethod_to_method mth)) as [preserve_methods _].
        change (C.premethod_annot mth) with (C.method_annot (CP.premethod_to_method mth)).
        eapply interface_reqs_method_cls; eauto.
        apply preserve_methods.
        exists mth.
        rewrite H0 in lookup'.  injection lookup' as eq'. subst pc'.
        auto.
        
        destruct (H c loaded).

      eapply interface_reqs_method_precls; eauto.

    apply (preserve iface c) in H.
    eapply interface_reqs_method_upcls; eauto.

    destruct (CP.class_loaded_dec classes' iface) as [[c loaded']|not_loaded].
      destruct (onlyadd iface c) as [[pc' [convert [lookup' not_before]]]|loaded]; eauto.
        rewrite H0 in lookup'.  injection lookup' as eq'. subst pc'.
        destruct (CP.preclass_to_class_props _ _ convert) as [_ [_ [methods [_ [_ ifaces]]]]].
        rewrite <- ifaces in H1.
        eapply interface_reqs_method_upcls; eauto.

        destruct (H c loaded).
        
      eapply interface_reqs_method_upprecls; eauto.

  intro new.
  induction new.
    destruct (onlyadd iface c) as [[pc' [convert [lookup' not_before]]]|loaded]; eauto.
      destruct (CP.preclass_to_class_props _ _ convert) as [_ [_ [methods _]]]. 
      destruct (methods mkey md) as [_ preserve_methods].
      destruct (preserve_methods H0) as [pm [pm_md has_pm]].
      frewrite (C.has_premethod_name has_pm).
      assert (annot_eq : C.method_annot md = C.premethod_annot pm). destruct pm.  inversion pm_md. auto.
      rewrite annot_eq.
      eapply interface_reqs_method_precls; eauto.

      eapply interface_reqs_method_cls; eauto.

    eapply interface_reqs_method_precls; eauto.
    intros c loaded.
    apply (preserve iface c) in loaded.
    apply (H c loaded).

    destruct (onlyadd iface c) as [[pc' [convert [lookup' not_before]]]|loaded]; eauto.
      destruct (CP.preclass_to_class_props _ _ convert) as [_ [_ [_ [_ [_ p_ifaces]]]]].
      rewrite p_ifaces in H0.
      eapply interface_reqs_method_upprecls; eauto.

      eapply interface_reqs_method_upcls; eauto.

    eapply interface_reqs_method_upprecls; eauto.
    intros c loaded.
    apply (preserve iface c) in loaded.
    apply (H c loaded).
Qed.

Lemma minimal_methodspec_preserved : forall classes classes' preclasses nm md mspec,
  CP.preserve_old_classes classes classes' ->
  CP.only_add_from_preclasses classes classes' preclasses ->
  (minimal_methodspec classes preclasses nm md mspec <->
   minimal_methodspec classes' preclasses nm md mspec).
Proof.
  intros until mspec.
  intros preserve onlyadd.
  split.

  intro old.
  induction old.
    destruct (CP.class_loaded_dec classes' nm) as [[c loaded']|not_loaded].
      destruct (onlyadd nm c) as [[pc' [convert [lookup' not_before]]]|loaded]; auto.
        rewrite H0 in lookup'.  injection lookup' as eq'. subst pc'.
        destruct (CP.preclass_to_class_props _ _ convert) as [_ [_ [p_methods [p_iface [_ _]]]]].
        rewrite <- p_iface in H1.
        eapply minimal_methodspec_loaded; eauto using A.sub_class_refl.
          eapply VM.lookup_minimal_refl; eauto.
          destruct (p_methods md (CP.premethod_to_method m)) as [p_methods' _].
          apply p_methods'.
          exists m.
          eauto.

          destruct m.  auto.

          destruct m.  auto.

        destruct (H c loaded).

      eapply minimal_methodspec_pre; eauto.

    eapply minimal_methodspec_loaded; eauto using A.preserve_subclass.
    eapply VM.lookup_minimal_preserved; eauto.

    destruct (CP.class_loaded_dec classes' nm) as [[c loaded']|not_loaded].
      destruct (onlyadd nm c) as [[pc' [convert [lookup' not_before]]]|loaded]; auto.
        rewrite H0 in lookup'.  injection lookup' as eq'. subst pc'.
        destruct (CP.preclass_to_class_props _ _ convert) as [_ [_ [p_methods [p_iface [p_super _]]]]].
        rewrite <- p_super in H2.
        rewrite <- p_iface in H3.
        destruct (CP.class_super_loaded _ _ _ _ loaded' H2) as [cS loaded_S].
        destruct IHold as [pc0 m notloaded| |pc0 nmS0 notloaded]; try destruct (notloaded cS loaded_S).
        rewrite (CP.class_loaded_unique H4 loaded_S) in *. clear H4.
        eapply minimal_methodspec_loaded.  eassumption. eassumption. eapply A.sub_class_step. eassumption. eassumption. eassumption.
          intros nmB' cB' assign1 assign2 loaded1 notint_B' B'nS0.
          apply A.get_sub_class with (cA:=c) (cB:=cB') in assign1; eauto.
          destruct assign1.
            rewrite (CP.class_loaded_unique loaded1 loaded') in *.  clear loaded'.
            case_eq (C.MethodList.lookup (C.class_methods c) md); auto.
            intros m' m'eq.
            right.
            destruct (proj2 (p_methods md m') m'eq) as [pm [pmeq premethod]].
            exists m'.  split; auto.
            destruct m'. inversion pmeq.
            simpl.
            apply (H1 pm premethod).

            rewrite (CP.class_loaded_unique H4 loaded') in *. clear H4.
            rewrite H2 in H13.  injection H13 as s_nm_eq. subst s_nm.
            unfold VM.lookup_minimal in H7. eapply H7; eauto.
              apply A.assignable_class_class with (cS:=cS) (cT:=cB'); auto.
              apply H8. apply H9. apply H10. apply H11. apply H12.
    
        destruct (H c loaded).

    eapply minimal_methodspec_prestep; eauto.

  intro new.
  induction new as [nm md mspec pc m notloaded nm_pc pc_notint has_m annot_m static_m |
                    nm md mspec c nmS cS m loaded notint_c subclass minimal loaded_s notint_s lookup_m annot_m static_m | ] .
    eapply minimal_methodspec_pre; eauto.
    intros c loaded.
    apply (preserve nm c) in loaded.
    apply (notloaded c loaded).

    destruct (onlyadd nm c) as [[pc' [convert [lookup' not_before]]]|loaded_before]; eauto.
      generalize c pc' loaded notint_c convert lookup'.
      clear c pc' loaded notint_c convert lookup'.
      induction subclass; intros;
      destruct (CP.preclass_to_class_props _ _ convert) as [_ [_ [p_methods [p_iface [p_super _]]]]].
        rewrite (CP.class_loaded_unique loaded_s loaded) in *.  clear H loaded_s.
        destruct (p_methods md m) as [_ preserve_methods].
        destruct (preserve_methods lookup_m) as [pm [m_pm has_pm]].
        assert (GA.method_spec (C.premethod_annot pm) = mspec).  destruct m. inversion m_pm. unfold C.premethod_annot. simpl in *. subst method_annot. auto.
        assert (C.premethod_static pm = false). destruct m. inversion m_pm. simpl in *. subst method_static. auto.
        eapply minimal_methodspec_pre; eauto.

        rewrite (CP.class_loaded_unique H loaded) in *. clear H.
        rewrite H0 in p_super.
        eapply minimal_methodspec_prestep; eauto.
          intros m' has_m'.
          unfold VM.lookup_minimal in minimal.
          assert (ass1:A.assignable classes' (C.ty_obj nm) (C.ty_obj nm)). eapply A.assignable_class_class; eauto using A.sub_class_step, A.sub_class_refl.  
          assert (ass2:A.assignable classes' (C.ty_obj nm) (C.ty_obj nm_t)). eapply A.assignable_class_class; eauto using A.sub_class_step, A.sub_class_refl.
          assert (nm_not_nm_t: nm<>nm_t). eapply A.subclass_distinct; eauto.
          destruct (p_methods md (CP.premethod_to_method m')) as [p_m _].
          destruct (minimal _ _ ass1 ass2 loaded notint_c nm_not_nm_t) as [nometh|[m1 [m1lookup m1static]]].
            rewrite p_m in nometh.
              discriminate.
              exists m'. auto.

              rewrite p_m in m1lookup.
                inversion m1lookup.
                destruct m1. simpl in *.  destruct m'.  inversion H1. subst method_static.
                reflexivity.

                exists m'. auto.

         assert (s_cls:exists c_s, CP.class_loaded classes' s_nm c_s) by (destruct subclass as [nmz c_s|nma nmb nmc c_s]; exists c_s; assumption).
         destruct s_cls as [c_snm loaded_snm].
         assert (s_notint:C.class_interface c_snm = false).  eapply CP.class_super_interface.  apply loaded. apply loaded_snm. assumption.
         destruct (onlyadd s_nm c_snm) as [[pc_snm [convert_s [lookup_s not_before_s]]]|loaded_before_s]; eauto.
           apply IHsubclass with (c:=c_snm) (pc':=pc_snm); eauto.
           apply VM.lookup_minimal_mid with (nmA:=nm); eauto.
           destruct subclass; eapply A.assignable_class_class; eauto using A.sub_class_step, A.sub_class_refl.
           eapply A.assignable_class_class; eauto.
           eauto using CP.class_super_interface.

           (* Establish that the class with the method was loaded before. *)
           destruct (top_is_nice classes s_nm nm_t c_snm) as [c_t [loaded_t notint_t]].
             eapply A.preserve_subclass_rev; eauto.
             assumption.
             assumption.
           rewrite (CP.class_loaded_unique loaded_s (preserve _ _ loaded_t)) in *.
           eapply minimal_methodspec_loaded.
             eassumption.  assumption. eapply A.preserve_subclass_rev. apply loaded_before_s. apply subclass. assumption.

             intros nmB' cB' assign1 assign2 loaded_B' notint_B' B'not_t.
             apply (minimal nmB' cB').  eapply A.assignable_trans. apply A.assignable_class_class with (nmT:=s_nm) (cS:=c0) (cT:=c_snm); auto.
             eauto using A.sub_class_refl, A.sub_class_step.  eapply A.preserve_assignable; eauto. eapply A.preserve_assignable; eauto.
             apply (preserve _ _ loaded_B'). assumption. assumption.
             
             eassumption. assumption. eassumption. assumption. assumption.

      apply minimal_methodspec_loaded with (c:=c) (nmS:=nmS) (cS:=cS) (m:=m);
      eauto using A.preserve_subclass_rev.
        intros nmB' cB' assign1 assign2 loaded_B' notint_B' B'notS.
        eapply minimal; eauto.  eapply A.preserve_assignable; eauto.
        eapply A.preserve_assignable; eauto.

        destruct (top_is_nice classes nm nmS c) as [cS' [loaded_s' _]];
        eauto using A.preserve_subclass_rev.
        rewrite (CP.class_loaded_unique loaded_s (preserve _ _ loaded_s')) in *.
        assumption.

    eapply minimal_methodspec_prestep; eauto.
      intros c loaded.
      destruct (H c (preserve _ _ loaded)).
Qed.

Lemma should_implement_preserved_rev : forall classes classes' preclasses nm iface,
  CP.preserve_old_classes classes classes' ->
  CP.only_add_from_preclasses classes classes' preclasses ->
  should_implement classes' preclasses nm iface ->
  should_implement classes preclasses nm iface.
Proof.
  intros until iface. intros preserve onlyadd.
  inversion 1; subst.
    destruct (onlyadd _ _ H0) as [[pc [pc_cA [lookup notloaded]]]|loaded].
      destruct (onlyadd _ _ H1) as [[pcB [pc_cB [lookupB notloadedB]]]|loadedB].
        destruct (CP.preclass_to_class_props _ _ pc_cB) as [_ [_ [_ [p_int [_ p_ints]]]]].
        rewrite p_ints in H4.
        eapply should_implement_pre; eauto.
        eapply pc_loaded_sub_class; eauto.

        eapply should_implement_cross; eauto.
        eapply pc_loaded_cross_sub_class; eauto.

      apply A.preserve_subclass_rev with (classesA:=classes) (c_s:=cA) in H3; eauto.
      destruct (A.superclass_loaded _ _ _ _ loaded H3) as [cB' loadedB].
      frewrite (CP.class_loaded_unique (preserve _ _ loadedB) H1).
      eapply should_implement_loaded with (nmB:=nmB); eauto.

    destruct (onlyadd _ _ H0) as [[pcB [pc_cB [lookupB notloadedB]]]|loadedB].
      destruct (CP.preclass_to_class_props _ _ pc_cB) as [_ [_ [_ [p_int [_ p_ints]]]]].
      eapply should_implement_pre; eauto.
      eapply pc_loaded_cross_super_class; eauto.
      rewrite p_ints in H3. assumption.

      eapply should_implement_cross; eauto using pc_preserve_cross_sub_class.

    eapply should_implement_pre; eauto using pc_preserve_sub_class.
    intros c loaded. apply (H0 c (preserve _ _ loaded)).
Qed.

Lemma convert_iface_req : forall classes preclasses nm iface c cI md m,
  CP.class_loaded classes nm c ->
  CP.class_loaded classes iface cI ->
  C.class_interface c = false ->
  C.class_interface cI = true ->
  A.assignable classes (C.ty_obj nm) (C.ty_obj iface) ->
  C.MethodList.lookup (C.class_methods cI) md = Some m ->
  exists base_iface,
    should_implement classes preclasses nm base_iface /\
    interface_reqs_method classes preclasses base_iface md (GA.method_spec (C.method_annot m)).
Proof.
  intros until m. intros loaded loaded_I not_iface is_iface assign lookup_m.
  destruct (A.get_class_implements _ _ _ _ _ loaded loaded_I not_iface is_iface assign) as [nm' [c' [loaded' [not_iface' [subclass has_iface]]]]].
  set (ifaces := C.class_interfaces c') in *.
  assert (Hifaces : forall x, In x ifaces -> In x (C.class_interfaces c')) by auto.
  clearbody ifaces.
  induction ifaces.
    inversion has_iface.

    inversion has_iface; subst.
      exists iface. split. eapply should_implement_loaded; eauto. apply Hifaces. simpl. auto.
      eapply interface_reqs_method_cls; eauto.

      exists a. split. eapply should_implement_loaded with (nmB:=nm'); eauto.  apply Hifaces. simpl. auto.
      set (ifaces_X := C.class_interfaces cX) in *.
      assert (Hx : forall x, In x ifaces_X -> In x (C.class_interfaces cX)) by auto.
      clearbody ifaces_X.
      generalize a cX H1 Hx.
      clear - loaded_I lookup_m H4.
      induction H4; intros.
        eapply interface_reqs_method_upcls; eauto.
        apply (Hx nmT). left. reflexivity.
        eapply interface_reqs_method_cls; eauto.

        eapply interface_reqs_method_upcls; eauto.  apply (Hx nmX). left. reflexivity.

        eapply IHdirect_super_interface; eauto.
        intros.  apply Hx. right. assumption.

      apply IHifaces; auto.
      intros.  apply Hifaces. right. assumption.
Qed.
      
End MkPreassignability.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import VirtualMethodLookupIface.
Require Import Twosig.
Require        OptionExt.
Require        BoolExt.

Require Import AnnotationIface.

Module MkVirtualMethodLookup (B  : BASICS)
                             (ANN : ANNOTATION B)
                             (C  : CLASSDATATYPES B ANN)
                             (CP : CLASSPOOL B ANN C)
                             (A  : ASSIGNABILITY B ANN C CP)
                           : VIRTUALMETHODLOOKUP B ANN C CP A.

(* virtual method lookup *)
Definition lookup_minimal : CP.cert_classpool -> B.Classname.t -> B.Classname.t -> (B.Methodname.t * C.descriptor) -> Prop
 := fun classes nmA nmB mdesc =>
    forall nmB' cB',
     A.assignable classes (C.ty_obj nmA) (C.ty_obj nmB') ->
     A.assignable classes (C.ty_obj nmB') (C.ty_obj nmB) ->
     CP.class_loaded classes nmB' cB' ->
     C.class_interface cB' = false ->
     nmB' <> nmB ->
        C.MethodList.lookup (C.class_methods cB') mdesc = None
     \/ exists m, C.MethodList.lookup (C.class_methods cB') mdesc = Some m /\ C.method_static m = true.

Lemma sub_classes_loaded : forall classes nmA cA nmB,
  CP.class_loaded classes nmA cA ->
  A.sub_class classes nmA nmB ->
  exists cB, CP.class_loaded classes nmB cB.
Proof.
  intros. generalize cA H.  clear cA H.
  induction H0.
    eauto.

    intros.
    destruct (CP.class_super_loaded _ _ _ _ H H0).
    eapply IHsub_class; eauto.
Qed.

Lemma lookup_minimal_preserved : forall classes classes' nmA cA nmB cB mdesc,
  CP.class_loaded classes nmA cA ->
  C.class_interface cA = false ->
  CP.class_loaded classes nmB cB ->
  C.class_interface cB = false ->
  lookup_minimal classes nmA nmB mdesc ->
  CP.preserve_old_classes classes classes' ->
  lookup_minimal classes' nmA nmB mdesc.
Proof.
  intros classes classes' nmA cA nmB cB mdesc loaded_A notint_A loaded_B notint_B old preserve nmB' cB' assign1 assign2 loaded' notint neq.
  unfold lookup_minimal in old.
  pose (preserve _ _ loaded_A).
  pose (preserve _ _ loaded_B).
  apply A.get_sub_class with (cA:=cA) (cB:=cB') in assign1; eauto.
  apply A.get_sub_class with (cA:=cB') (cB:=cB) in assign2; eauto.
  apply A.preserve_subclass_rev with (classesA:=classes) (c_s:=cA) in assign1; eauto.
  destruct (sub_classes_loaded _ _ _ _ loaded_A assign1) as [cB'' loaded_B'].
  rewrite (CP.class_loaded_unique (preserve _ _ loaded_B') loaded') in loaded_B'.
  apply A.preserve_subclass_rev with (classesA:=classes) (c_s:=cB') in assign2; eauto.
  eapply old; eauto;
  eapply A.assignable_class_class; eauto.
Qed.

Definition lookup_minimal_inner : CP.cert_classpool -> B.Classname.t -> B.Classname.t -> (B.Methodname.t * C.descriptor) -> Prop
 := fun classes nmA nmB mdesc =>
    forall nmB' cB',
     A.sub_class classes nmA nmB' ->
     A.sub_class classes nmB' nmB ->
     CP.class_loaded classes nmB' cB' ->
     nmB' <> nmB ->
        C.MethodList.lookup (C.class_methods cB') mdesc = None
     \/ exists m, C.MethodList.lookup (C.class_methods cB') mdesc = Some m /\ C.method_static m = true.

Inductive sub_class_strict (classes:CP.cert_classpool) : B.Classname.t -> B.Classname.t -> Prop :=
| sub_class_s_one : forall nm c s_nm,
   CP.class_loaded classes nm c ->
   C.class_super_class c = Some s_nm ->
   sub_class_strict classes nm s_nm
| sub_class_s_step : forall nm nm_t s_nm c,
   CP.class_loaded classes nm c ->
   C.class_super_class c = Some s_nm ->
   sub_class_strict classes s_nm nm_t ->
   sub_class_strict classes nm nm_t.

Lemma scs_has_super : forall classes A cA B,
  CP.class_loaded classes A cA ->
  sub_class_strict classes A B ->
  exists C, C.class_super_class cA = Some C.
intros. destruct H0; exists s_nm; rewrite (CP.class_loaded_unique H H0) in *; assumption.
Save.

Lemma sub_class_strict_trans : forall classes A B C,
  sub_class_strict classes A B ->
  sub_class_strict classes B C ->
  sub_class_strict classes A C.
intros classes A B C. induction 1; eauto using sub_class_s_step.
Save.

Lemma sc_shift_up : forall classes A cA S,
  sub_class_strict classes A A ->
  CP.class_loaded classes A cA ->
  C.class_super_class cA = Some S ->
  sub_class_strict classes S S.
intros classes A cA S A_A A_exists A_S.
inversion A_A.
 subst. rewrite (CP.class_loaded_unique H A_exists) in *. rewrite A_S in H0. inversion H0. assumption.
 subst. rewrite (CP.class_loaded_unique H A_exists) in *. rewrite A_S in H0. inversion H0. subst.
 eapply sub_class_strict_trans.
  apply H1.
  eapply sub_class_s_one. apply A_exists. assumption.
Save.

Lemma sub_class_no_loops : forall classes A cA,
  sub_class_strict classes A A ->
  CP.class_loaded classes A cA ->
  CP.super_class_chain classes (C.class_super_class cA) ->
  False.
intros classes A cA A_subs_A A_exists scc.
set (Asuper := C.class_super_class cA). pose (e2:=refl_equal Asuper:C.class_super_class cA=Asuper). 
generalize Asuper e2. clear Asuper e2. intros.
rewrite e2 in scc.
generalize A cA A_exists A_subs_A e2. clear A cA A_exists A_subs_A e2.
induction scc; intros.
 destruct (scs_has_super _ _ _ _ A_exists A_subs_A) as [C csc_C]. rewrite csc_C in e2. discriminate.
 apply (H2 _ H nm c); eauto using sc_shift_up.
Save.

Lemma soft_to_strict : forall classes A cA B C,
  CP.class_loaded classes A cA ->
  C.class_super_class cA = Some B ->
  A.sub_class classes B C ->
  sub_class_strict classes A C.
intros classes A cA B C A_exists cA_B B_C.
generalize A cA A_exists cA_B. clear A cA A_exists cA_B.
induction B_C; intros.
 eapply sub_class_s_one; eassumption.
 eapply sub_class_s_step; eauto.
Save.

Lemma sub_class_antisymmetric : forall classes A B cA,
  CP.class_loaded classes A cA ->
  C.class_interface cA = false ->
  A.sub_class classes A B ->
  A.sub_class classes B A ->
  A = B.
intros classes A B cA A_Exists A_class A_sub_B B_sub_A.
destruct A_sub_B as [|A A' B cA' A_exists Asuper_link A'_sub_B].
 reflexivity.
 elimtype False. eapply sub_class_no_loops.
  eapply soft_to_strict.
   apply A_exists.
   apply Asuper_link.
   eapply A.sub_class_trans; eassumption.
  apply A_exists.
  eapply CP.cert_classpool_gives_scc.
   apply A_exists.
   rewrite (CP.class_loaded_unique A_Exists A_exists) in *. assumption.
Save.

Lemma lookup_minimal_refl : forall classes nm md c,
  CP.class_loaded classes nm c ->
  C.class_interface c = false ->
  lookup_minimal classes nm nm md.
Proof.
  intros.
  intros nm' c' assign1 assign2 loaded' notint' noteq.
  apply (A.get_sub_class _ _ _ _ _ H loaded' H0 notint') in assign1.
  apply (A.get_sub_class _ _ _ _ _ loaded' H notint' H0) in assign2.
  rewrite (sub_class_antisymmetric _ _ nm' _ H H0 assign1 assign2) in *; auto.
  destruct noteq. reflexivity.
Qed.

Lemma lookup_minimal_mid : forall classes nmA nmB nmB' md,
  A.assignable classes (C.ty_obj nmA) (C.ty_obj nmB') ->
  A.assignable classes (C.ty_obj nmB') (C.ty_obj nmB) ->
  lookup_minimal classes nmA nmB md ->
  lookup_minimal classes nmB' nmB md.
Proof.
  intros.
  unfold lookup_minimal in *.
  intros.
  apply H1 with (nmB':=nmB'0) (cB':=cB'); auto.
  apply A.assignable_trans with (b:=(C.ty_obj nmB'));assumption.
Qed.

Lemma fixed_sub_class_refl_with_min : forall classes nm c d,
  CP.class_loaded classes nm c ->
  C.class_interface c = false ->
  A.sub_class classes nm (C.class_name c) /\ lookup_minimal_inner classes nm (C.class_name c) d.
intros. rewrite (CP.cert_classpool_names_2 H). split.
 eapply A.sub_class_refl. eauto.
 unfold lookup_minimal_inner. intros.
 elimtype False. apply H4. symmetry. eapply sub_class_antisymmetric; eassumption.
Defined.
Implicit Arguments fixed_sub_class_refl_with_min [classes nm c].

Lemma step_subclassing : forall classes nm c x d m,
  CP.class_loaded classes nm c ->
  C.MethodList.lookup (C.class_methods c) d = Some m ->
  C.method_static m = true ->
  (exists s_nm, C.class_super_class c = Some s_nm /\ A.sub_class classes s_nm x /\ lookup_minimal_inner classes s_nm x d) ->
  A.sub_class classes nm x /\ lookup_minimal_inner classes nm x d.
intros classes nm c x d m c_exists m_exists m_static [s_nm [s_nm_eq [s_sub_x min]]].
split.
 (* sub_class *)
 eapply A.sub_class_step; eassumption.
 (* lookup_minimal *)
 unfold lookup_minimal_inner.
 intros nmB' cB' nm_sub_nmB' nmB'_sub_x B'_exists B'_neq_x.
 destruct (B.Classname.eq_dec nmB' nm) as [B'_eq_nm | B'_neq_nm].
  (* nm = B *)
  subst. right. rewrite (CP.class_loaded_unique c_exists B'_exists) in *. exists m; split; assumption.
  (* nm <> B *)
  destruct nm_sub_nmB'.
   (* nm = B' : contradiction *)
   elimtype False. apply B'_neq_nm. reflexivity.
   (* nm < B' *)
   rewrite (CP.class_loaded_unique H c_exists) in *.
   rewrite s_nm_eq in H0. inversion H0. subst.
   destruct (min nm_t cB' nm_sub_nmB' nmB'_sub_x B'_exists B'_neq_x); auto.
Save.
Implicit Arguments step_subclassing [classes nm c x d m].

Lemma step_subclassing_2 : forall classes nm c x d,
  CP.class_loaded classes nm c ->
  C.MethodList.lookup (C.class_methods c) d = None ->
  (exists s_nm, C.class_super_class c = Some s_nm /\ A.sub_class classes s_nm x /\ lookup_minimal_inner classes s_nm x d) ->
  A.sub_class classes nm x /\ lookup_minimal_inner classes nm x d.
intros classes nm c x d c_exists m_not_exists [s_nm [s_nm_eq [s_sub_x min]]].
split.
 (* sub_class *)
 eapply A.sub_class_step; eassumption.
 (* lookup_minimal *)
 unfold lookup_minimal_inner.
 intros nmB' cB' nm_sub_nmB' nmB'_sub_x B'_exists B'_neq_x.
 destruct (B.Classname.eq_dec nmB' nm) as [B'_eq_nm | B'_neq_nm].
  (* nm = B *)
  subst. left. rewrite (CP.class_loaded_unique c_exists B'_exists) in *. assumption.
  (* nm <> B *)
  destruct nm_sub_nmB'.
   (* nm = B' : contradiction *)
   elimtype False. apply B'_neq_nm. reflexivity.
   (* nm < B' *)
   rewrite (CP.class_loaded_unique H c_exists) in *.
   rewrite s_nm_eq in H0. inversion H0. subst.
   destruct (min nm_t cB' nm_sub_nmB' nmB'_sub_x B'_exists B'_neq_x); auto.
Save.
Implicit Arguments step_subclassing_2 [classes nm c x d].

Fixpoint lookup_virtual_method_aux (classes:CP.cert_classpool)
                                   (nm:option B.Classname.t)
                                   (d:B.Methodname.t * C.descriptor)
                                   (scc:CP.super_class_chain classes nm)
                                   {struct scc}
                                 : option { c : C.class, m : C.method |
                                         CP.class_loaded classes (C.class_name c) c /\
                                         C.MethodList.lookup (C.class_methods c) d = Some m /\
                                         C.class_interface c = false /\
                                         C.method_static m = false /\
                                         (exists s_nm, nm = Some s_nm /\ A.sub_class classes s_nm (C.class_name c)
                                                                      /\ lookup_minimal_inner classes s_nm (C.class_name c) d) }
 :=
 let P2 := fun c s_nm => nm = Some s_nm /\ A.sub_class classes s_nm (C.class_name c) /\ lookup_minimal_inner classes s_nm (C.class_name c) d in
 let P := fun c m => CP.class_loaded classes (C.class_name c) c /\
                     C.MethodList.lookup (C.class_methods c) d = Some m /\
                     C.class_interface c = false /\
                     C.method_static m = false /\
                     ex (P2 c) in
 match OptionExt.option_informative nm with
 | inleft (exist s_nm s_nm_eq) =>
    match CP.class_loaded_dec classes s_nm with
    | inleft (exist sc sc_exists) =>
       let scc_super := CP.super_class_chain_inv sc_exists s_nm_eq scc in
       match C.MethodList.lookup_informative (C.class_methods sc) d with
       | inleft (exist m m_exists) =>
          match BoolExt.bool_informative (C.method_static m) with
          | left is_static =>
             match lookup_virtual_method_aux classes (C.class_super_class sc) d scc_super with
             | Some (pack2 c m (conj c_exists (conj m_exists' (conj c_class (conj m_instance sub_class_proof))))) =>
                let sub_class_proof' := ex_intro (P2 c) s_nm (conj s_nm_eq (step_subclassing sc_exists m_exists is_static sub_class_proof)) in
                Some (pack2 P c m (conj c_exists (conj m_exists' (conj c_class (conj m_instance sub_class_proof')))))
             | None =>
                None
             end
          | right not_static =>
             let not_interface := CP.scc_gives_class s_nm_eq scc sc_exists in
             let sub_class_proof := ex_intro (P2 sc) s_nm (conj s_nm_eq (fixed_sub_class_refl_with_min d sc_exists not_interface)) in
             let sc_exists := CP.cert_classpool_names sc_exists in
             Some (pack2 P sc m (conj sc_exists (conj m_exists (conj not_interface (conj not_static sub_class_proof)))))
          end
       | inright m_not_exists =>
          match lookup_virtual_method_aux classes (C.class_super_class sc) d scc_super with
          | Some (pack2 c m (conj c_exists (conj m_exists (conj c_class (conj m_instance sub_class_proof))))) =>
             let sub_class_proof' := ex_intro (P2 c) s_nm (conj s_nm_eq (step_subclassing_2 sc_exists m_not_exists sub_class_proof)) in
             Some (pack2 P c m (conj c_exists (conj m_exists (conj c_class (conj m_instance sub_class_proof')))))
          | None =>
             None
          end
       end
    | inright not_there =>
       let not_not_there := CP.super_class_chain_not_not_there s_nm_eq scc in
       match not_not_there not_there with end
    end
 | inright _ =>
    None
 end.

Lemma evidence_gives_class : forall classes nm c',
  (exists c, CP.class_loaded classes nm c /\ C.class_interface c = false) ->
  CP.class_loaded classes nm c' ->
  C.class_interface c' = false.
intros classes nm c' evidence c'_exists.
destruct evidence as [c [c_exists c_class]].
rewrite (CP.class_loaded_unique c'_exists c_exists) in *. assumption.
Save.
Implicit Arguments evidence_gives_class [classes nm c'].

Lemma evidence_gives_not_not_there : forall classes nm,
  (exists c, CP.class_loaded classes nm c /\ C.class_interface c = false) ->
  ~(~(exists c, CP.class_loaded classes nm c)).
intros classes nm [c [evidence X]].
eauto.
Save.
Implicit Arguments evidence_gives_not_not_there [classes nm].

Lemma get_assignable_and_lookup_minimal : forall classes A B cA cB mdesc,
  CP.class_loaded classes A cA ->
  CP.class_loaded classes B cB ->
  C.class_interface cA = false ->
  C.class_interface cB = false ->
  A.sub_class classes A B /\ lookup_minimal_inner classes A B mdesc ->
  A.assignable classes (C.ty_obj A) (C.ty_obj B) /\ lookup_minimal classes A B mdesc.
intros classes A B cA cB mdesc A_exists B_exists A_class B_class [nm_x min].
split.
 eapply A.assignable_class_class; eassumption.
 unfold lookup_minimal. intros B' cB' A_nmB' nmB'_B B'_exists B'_class neq.
 unfold lookup_minimal_inner in min. eapply min.
  eapply A.get_sub_class; try eassumption.
  eapply A.get_sub_class; try eassumption.
  assumption.
  assumption.
Save.
Implicit Arguments get_assignable_and_lookup_minimal [classes A B cA cB mdesc].

(* FIXME: need to do method overriding properly for generics *)
Definition lookup_virtual_method : forall classes nm d,
  (exists c, CP.class_loaded classes nm c /\ C.class_interface c = false) ->
  option { c : C.class, m : C.method |
     CP.class_loaded classes (C.class_name c) c /\
     C.MethodList.lookup (C.class_methods c) d = Some m /\
     C.class_interface c = false /\
     C.method_static m = false /\
     A.assignable classes (C.ty_obj nm) (C.ty_obj (C.class_name c)) /\
     lookup_minimal classes nm (C.class_name c) d }
 :=
 fun classes nm d evidence =>
 let P := fun c m => CP.class_loaded classes (C.class_name c) c /\
                     C.MethodList.lookup (C.class_methods c) d = Some m /\
                     C.class_interface c = false /\
                     C.method_static m = false /\
                     A.assignable classes (C.ty_obj nm) (C.ty_obj (C.class_name c)) /\
                     lookup_minimal classes nm (C.class_name c) d
 in
 match CP.class_loaded_dec classes nm with
 | inleft (exist c c_exists) =>
    let is_class := evidence_gives_class evidence c_exists in
    let scc := CP.cert_classpool_gives_scc c_exists is_class in
    match C.MethodList.lookup_informative (C.class_methods c) d with
    | inleft (exist m m_exists) => (* FIXME: collapse these two to avoid code duplication below *)
       match BoolExt.bool_informative (C.method_static m) with
       | right is_instance =>
          let c_exists' := CP.cert_classpool_names c_exists in
          let sub_class_proof := fixed_sub_class_refl_with_min d c_exists is_class in
          let assignable_proof := get_assignable_and_lookup_minimal c_exists c_exists' is_class is_class sub_class_proof in
          Some (pack2 P c m (conj c_exists' (conj m_exists (conj is_class (conj is_instance assignable_proof)))))
       | left is_static =>
          match lookup_virtual_method_aux classes (C.class_super_class c) d scc with
          | Some (pack2 c' m (conj c'_exists (conj m_exists' (conj is_class2 (conj is_instance sub_class_proof))))) =>
             let sub_class_proof' := step_subclassing c_exists m_exists is_static sub_class_proof in
             let assignable_proof := get_assignable_and_lookup_minimal c_exists c'_exists is_class is_class2 sub_class_proof' in
             Some (pack2 P c' m (conj c'_exists (conj m_exists' (conj is_class2 (conj is_instance assignable_proof)))))
          | None =>
             None
          end
       end
    | inright no_m =>
       match lookup_virtual_method_aux classes (C.class_super_class c) d scc with
       | Some (pack2 c' m (conj c'_exists (conj m_exists (conj is_class2 (conj is_instance sub_class_proof))))) =>
          let sub_class_proof' := step_subclassing_2 c_exists no_m sub_class_proof in
          let assignable_proof := get_assignable_and_lookup_minimal c_exists c'_exists is_class is_class2 sub_class_proof' in
          Some (pack2 P c' m (conj c'_exists (conj m_exists (conj is_class2 (conj is_instance assignable_proof)))))
       | None =>
          None
       end
    end
 | inright not_there =>
    let not_not_there := evidence_gives_not_not_there evidence in
    match not_not_there not_there with end
 end.

End MkVirtualMethodLookup.

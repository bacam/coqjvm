Require Import ClasspoolIface.
Require Import ClassDatatypesIface.
Require Import AssignabilityIface.
Require Import PreassignabilityIface.
Require Import BasicMachineTypes.
Require Import OptionExt.
Require Import MLStrings.
Require Import ErrorMonad.
Require Import ErrorMessages.
Require Import Twosig.
Require Import FMaps.
Require Import RelationUtils.
Require Import Bool.
Require Import VirtualMethodLookupIface.
Require Import GenericAnnotationIface.
Require FMapAVL.
Require FMapOverlay.
Require FMapFacts.

Inductive every (A:Type) (P:A->Prop) : list A -> Prop :=
| ev_nil  : every A P nil
| ev_cons : forall x xs, P x -> every A P xs -> every A P (x::xs).
Implicit Arguments every [A].

Module Type OVERRIDECHECKERBASE
  (B : BASICS)
  (GA : GENERIC_ANNOTATION B)
  (C  : CLASSDATATYPES B GA.A)
  (CP : CLASSPOOL B GA.A C).

Parameter vcset : Type.
Parameter vcset_empty : vcset.
Parameter vcset_ok : vcset -> Prop.
Parameter vcset_union : vcset -> vcset -> vcset.
Parameter vcset_union_ok1 : forall vcs vcs', vcset_ok (vcset_union vcs vcs') -> vcset_ok vcs.
Parameter vcset_union_ok2 : forall vcs vcs', vcset_ok (vcset_union vcs vcs') -> vcset_ok vcs'.
Parameter vcset_union_ok3 : forall vcs vcs', vcset_ok vcs -> vcset_ok vcs' -> vcset_ok (vcset_union vcs vcs').

Parameter safe_override : GA.method_specification -> GA.method_specification -> Prop.
Parameter safe_override_refl : forall s,
  safe_override s s.
Parameter safe_override_trans : forall s1 s2 s3,
  safe_override s1 s2 ->
  safe_override s2 s3 ->
  safe_override s1 s3.

Parameter check_override : (B.Classname.t*B.Methodname.t) -> GA.A.class_annotation -> GA.method_specification -> GA.method_specification -> error_monad vcset.

Parameter check_override_ok : forall src ca s1 s2 vcs,
  check_override src ca s1 s2 = Val vcs ->
  vcset_ok vcs ->
  safe_override s1 s2.

End OVERRIDECHECKERBASE.


Module GenericOverrideChecker (B   : BASICS)
                              (GA  : GENERIC_ANNOTATION B)
                              (C   : CLASSDATATYPES   B GA.A)
                              (CP  : CLASSPOOL        B GA.A C)
                              (A   : ASSIGNABILITY    B GA.A C CP)
                              (OCB : OVERRIDECHECKERBASE B GA C CP)
                              (VM  : VIRTUALMETHODLOOKUP B GA.A C CP A)
                              (PA  : PREASSIGNABILITY B GA C CP A VM).

Import OCB.

Module MethodDesc : UsualOrderedType with Definition t := (B.Methodname.t * C.descriptor)%type
       := PairUsualOrderedType B.Methodname C.Descriptor_as_UOT.

Module SpecTable : FMapInterface.S with Module E := MethodDesc := FMapAVL.Make MethodDesc.
Module SpecTableFacts := FMapFacts.Facts SpecTable.

Module STOverlay := FMapOverlay.MakeOverlay SpecTable.
Module ClassTable : FMapInterface.S with Definition E.t := B.Classname.t := FMapAVL.Make B.Classname.


Definition premethod_spec m := GA.method_spec (C.premethod_annot m).
Definition method_spec m :=  GA.method_spec (C.method_annot m).


Definition descriptor_eq_dec : forall (d d':C.descriptor), {d=d'}+{d<>d'}.
intros. destruct (C.Descriptor_as_UOT.compare d d').
 right. apply C.Descriptor_as_UOT.lt_not_eq. apply l.
 left. apply e.
 right. unfold not. intros. symmetry in H. generalize H. apply C.Descriptor_as_UOT.lt_not_eq. apply l.
Save.

Definition mdesc_eq_dec : forall (d d' : B.Methodname.t * C.descriptor), {d=d'}+{d<>d'}.
decide equality. apply descriptor_eq_dec. apply B.Methodname.eq_dec.
Save.

Definition check_vc := fold_err vcset vcset_union.
Definition check_vc_ok := fold_err_ok vcset vcset_ok vcset_union vcset_union_ok1 vcset_union_ok2.
Implicit Arguments check_vc [B].
Implicit Arguments check_vc_ok [B f l a r].

Fixpoint scan_methods (clsnm : B.Classname.t)
                      (class_annot : GA.A.class_annotation)
                      (m_list : list C.premethod)
                      (seen : list (B.Methodname.t * C.descriptor))
                      (specs specs' : SpecTable.t GA.method_specification)
                      (vcs : vcset) {struct m_list}
                      : error_monad (SpecTable.t GA.method_specification*vcset) :=
 match m_list with
 | nil =>
    ret (specs',vcs)
 | mimpl::m_list =>
   match B.Methodname.eq_dec (C.premethod_name mimpl) B.init with
     | left _ =>
       (* skip <init> *)
       scan_methods clsnm class_annot m_list seen specs specs' vcs
     | right _ =>
       let thisspec := premethod_spec mimpl in
       let mdesc := (C.premethod_name mimpl, C.premethod_descriptor mimpl) in
       match In_dec mdesc_eq_dec mdesc seen with
         | left _ =>
           fail (err_duplicate_method mlapp (B.Methodname.to_string (C.premethod_name mimpl)))
         | right _ =>
           if C.premethod_static mimpl then scan_methods clsnm class_annot m_list (mdesc::seen) specs specs' vcs else
             let newspecs := SpecTable.add mdesc thisspec specs' in
             match SpecTable.find mdesc specs with
               | None => (* This method is new in this class: no overriding to check *)
                 scan_methods clsnm class_annot m_list (mdesc::seen) specs newspecs vcs
               | Some spec =>
                 vcs' <- tagfailure (err_overriding_failure mlapp (B.Methodname.to_string (C.premethod_name mimpl))) (check_override (clsnm,C.premethod_name mimpl) class_annot thisspec spec);:
                 scan_methods clsnm class_annot m_list (mdesc::seen) specs newspecs (vcset_union vcs vcs')
             end
       end
   end
 end.
   

Definition premethod_safe_override := fun specs meth =>
  C.premethod_name meth = B.init
  \/
  C.premethod_static meth = true
  \/
  (C.premethod_name meth <> B.init
    /\
    (~SpecTable.In (C.premethod_name meth, C.premethod_descriptor meth) specs
      \/
      forall spec,
        SpecTable.MapsTo (C.premethod_name meth, C.premethod_descriptor meth) spec specs ->
      safe_override (premethod_spec meth) spec)).

Lemma scan_methods_vc_accumulate :  forall src class_annot m_list seen specs specs' specs'' vcs vcs',
 scan_methods src class_annot m_list seen specs specs' vcs = Val (specs'',vcs') ->
 vcset_ok vcs' ->
 vcset_ok vcs.
induction m_list; intros.
 simpl in H. inversion H. subst. assumption.
 simpl in H. destruct (B.Methodname.eq_dec (C.premethod_name a) B.init).
  eapply IHm_list; eauto.
  destruct (In_dec mdesc_eq_dec (C.premethod_name a, C.premethod_descriptor a) seen). discriminate.
  destruct (C.premethod_static a).
   eapply IHm_list; eauto.
   destruct (SpecTable.find (C.premethod_name a, C.premethod_descriptor a) specs).
    destruct_err (check_override (src, C.premethod_name a) class_annot (premethod_spec a) m) H vcs'' vcs''eq.
     eapply vcset_union_ok1. eapply IHm_list; eauto.
     eapply IHm_list; eauto.
Qed.

Lemma scan_methods_ok : forall src class_annot m_list seen specs specs' specs'' vcs vcs',
 scan_methods src class_annot m_list seen specs specs' vcs = Val (specs'',vcs') ->
 vcset_ok vcs' ->
 every (premethod_safe_override specs) m_list.
induction m_list; intros.
 (* Empty list *)
 constructor.
 (* cons *)
 destruct a. simpl in H.
 destruct (B.Methodname.eq_dec premethod_name B.init) as [eq_init|neq_init].
  (* this method is <init> *)
  constructor. left. simpl. assumption. eauto.
  (* this method is not <init> *)
  match goal with [_:(if ?x then _ else _) = _ |- _ ] => destruct x; try discriminate end.
  destruct premethod_static.
    constructor.
     right; left; reflexivity. eapply IHm_list. eassumption. assumption.
   destruct (option_informative (SpecTable.find (premethod_name, premethod_descriptor) specs))
         as [[spec find_spec] | find_spec]; rewrite find_spec in H.
   (* We are overriding some method *)
    unfold premethod_spec in H. simpl in H.
    destruct_err (check_override (src,premethod_name) class_annot (GA.method_spec premethod_annot) spec) H x check_res.
    constructor.
     right. right. split. assumption. right. simpl. intros.
      assert (SpecTable.find (premethod_name, premethod_descriptor) specs = Some spec0). apply SpecTable.find_1. assumption.
      rewrite find_spec in H2. inversion H2. subst. eapply check_override_ok. eassumption. eapply vcset_union_ok2. eapply scan_methods_vc_accumulate; eassumption.
     eapply IHm_list. apply H. assumption.
    (* This method is new in this hierarchy *)
    constructor.
     right. right. split. assumption. left. simpl. unfold not. intros. destruct H1.
       assert (SpecTable.find (premethod_name, premethod_descriptor) specs = Some x). apply SpecTable.find_1. assumption.
       rewrite H2 in find_spec. discriminate.
     eapply IHm_list. apply H. assumption.
Save.

Lemma not_In_add : forall m m' (s:GA.method_specification) specs,
 ~SpecTable.In m (SpecTable.add m' s specs) ->
 m' <> m /\ ~SpecTable.In m specs.
intros m m' s specs not_In_add.
destruct (mdesc_eq_dec m' m).
 subst. elimtype False. apply not_In_add. exists s. apply SpecTable.add_1. apply MethodDesc.eq_refl.
 split; auto.
  unfold not. intro. apply not_In_add. destruct H. exists x. apply SpecTable.add_2. apply n. apply H.
Save.

Lemma pair_neq : forall (a1 a2:B.Methodname.t) (b1 b2:C.descriptor), (a1,b1)<>(a2,b2) -> a1 <> a2 \/ b1 <> b2.
intros. destruct (B.Methodname.eq_dec a1 a2); destruct (descriptor_eq_dec b1 b2); intuition congruence.
Save.

Lemma tail_doesnt_have : forall a l mdesc,
 (forall m, ~C.has_premethod (a::l) mdesc m) ->
 forall m, ~C.has_premethod l mdesc m.
unfold not. intros. 
destruct a.
destruct mdesc.
destruct (mdesc_eq_dec (premethod_name, premethod_descriptor) (t,d)).
 eapply H. inversion e. subst. apply C.has_premethod_cons_1.
 eapply H. constructor.
  apply H0.
  apply pair_neq. apply n.
Save.

Lemma find_None_is_not_In : forall m s,
 SpecTable.find m s = None (A:=GA.method_specification) ->
 ~SpecTable.In m s.
intros m s find_None.
unfold not. intro. destruct H. rewrite (SpecTable.find_1 H) in find_None. discriminate.
Save.

Lemma scan_methods_ok2_aux : forall src class_annot m_list seen specs specs' specs'',
 (forall mdesc spec, SpecTable.MapsTo mdesc spec specs' -> fst mdesc <> B.init) ->
 (forall mdesc spec, SpecTable.MapsTo mdesc spec specs' -> In mdesc seen) ->
 (exists vcs, exists vcs',
  scan_methods src class_annot m_list seen specs specs' vcs = Val (specs'',vcs')) ->
 forall mdesc spec,
  SpecTable.MapsTo mdesc spec specs'' <->
  fst mdesc <> B.init /\ (SpecTable.MapsTo mdesc spec specs' \/ (~SpecTable.In mdesc specs' /\ ~In mdesc seen /\ exists m, C.has_premethod m_list mdesc m /\ C.premethod_static m = false /\ premethod_spec m = spec)).
induction m_list.
 (* empty list *)
 intros seen specs specs' specs'' no_init seen_specs [vcs [vcs' scan_res]] mdesc spec. 
 simpl in scan_res. inversion scan_res. subst. clear scan_res. split; intro.
  split.
   eauto.
   left. assumption.
  destruct H as [not_init [X|X]].
   assumption. 
   destruct X as [_ [_ [m [H _]]]]. inversion H.
 (* step case *)
 intros seen specs specs' specs'' no_init seen_specs [vcs [vcs' scan_res]] mdesc spec. 
 destruct a. simpl in scan_res.
 set (m:=(C.mkPreMethod premethod_name premethod_descriptor
                       premethod_public premethod_protected premethod_private
                       premethod_abstract premethod_static premethod_final
                       premethod_synchronized premethod_strict premethod_code
                       premethod_annot)) in *.
 destruct (B.Methodname.eq_dec premethod_name B.init) as [eq_init|neq_init].
  (* skipping this method because it's init *)
  assert (X:SpecTable.MapsTo mdesc spec specs'' <->
    fst mdesc <> B.init /\
    (SpecTable.MapsTo mdesc spec specs' \/
      ~ SpecTable.In mdesc specs' /\
      ~ In mdesc seen /\
      (exists m0 : C.premethod,
        C.has_premethod m_list mdesc m0 /\ C.premethod_static m0 = false /\ premethod_spec m0 = spec))).
   eauto using IHm_list.
   split; intro.
    rewrite X in H. intuition.
     right. intuition. destruct H9 as [m' [X1 X2]]. exists m'. intuition. unfold m. destruct m'. destruct mdesc. apply C.has_premethod_cons_2. 
      assumption.
      left. subst premethod_name. eauto.
    rewrite X. intuition.
     right. intuition. destruct H5 as [m' [X1 X2]]. exists m'. intuition. inversion X1.
      elimtype False. unfold m in *. subst. simpl in *. apply H0. reflexivity.
      assumption.
  (* skipping this method because it's static *)
  destruct premethod_static.
  match goal with [_:(if ?x then _ else _) = _ |- _ ] => destruct x; try discriminate end.
  assert (Y:forall mdesc spec, SpecTable.MapsTo mdesc spec specs' -> In mdesc ((premethod_name, premethod_descriptor)::seen)).
   intros. right. apply (seen_specs _ _ H).
  assert (X:SpecTable.MapsTo mdesc spec specs'' <->
    fst mdesc <> B.init /\
    (SpecTable.MapsTo mdesc spec specs' \/
      ~ SpecTable.In mdesc specs' /\
      ~ In mdesc ((premethod_name, premethod_descriptor)::seen) /\
      (exists m0 : C.premethod,
        C.has_premethod m_list mdesc m0 /\ C.premethod_static m0 = false /\ premethod_spec m0 = spec))).
   eauto using IHm_list.
   split; intro.
    rewrite X in H. intuition.
     right. intuition. destruct H9 as [m' [X1 X2]]. exists m'. intuition. unfold m. destruct m'. destruct mdesc. apply C.has_premethod_cons_2. 
      assumption.
      destruct (B.Methodname.eq_dec premethod_name t). right. intro. destruct H6. subst t d. left. reflexivity.
      left. assumption.
    rewrite X. intuition.
     right. intuition. 
      destruct H6.
        subst mdesc. destruct H5 as [m' [X1 [X2 X3]]]. inversion X1; subst; try discriminate. destruct H22 as [silly|silly]; destruct silly; reflexivity.
        apply (H3 H6).
      destruct H5 as [m' [X1 [X2 X3]]]. exists m'. intuition. inversion X1.
      subst. discriminate. assumption.
  (* not skipping this method *)
  match goal with [_:(if ?x then _ else _) = _ |- _ ] => destruct x; try discriminate end.
  assert (X:SpecTable.MapsTo mdesc spec specs'' <->
          fst mdesc <> B.init /\
          (SpecTable.MapsTo mdesc spec (SpecTable.add (premethod_name, premethod_descriptor) (premethod_spec m) specs') \/
           ~ SpecTable.In mdesc (SpecTable.add (premethod_name, premethod_descriptor) (premethod_spec m) specs') /\
           ~ In mdesc ((premethod_name, premethod_descriptor)::seen) /\
           (exists m : C.premethod,
              C.has_premethod m_list mdesc m /\ C.premethod_static m = false /\ premethod_spec m = spec))).
   apply (IHm_list ((premethod_name, premethod_descriptor)::seen) specs (SpecTable.add (premethod_name, premethod_descriptor) (premethod_spec m) specs')).
    intros. rewrite SpecTableFacts.add_mapsto_iff in H. destruct H as [[mdesc_eq _]|[_ in_specs']].
     rewrite <- mdesc_eq. simpl. assumption.
     eauto.
    intros. destruct (proj1 (SpecTableFacts.add_mapsto_iff _ _ _ _ _) H) as [[mdesc0_eq annot_eq]|[mdesc0_neq maps']].
     destruct mdesc0_eq. left. reflexivity.
     right. eapply seen_specs; eauto.
    destruct (option_informative (SpecTable.find (premethod_name, premethod_descriptor) specs))
          as [[spec' find_spec] | find_spec]; rewrite find_spec in scan_res.
     destruct_err (check_override (src,premethod_name) class_annot (premethod_spec m) spec') scan_res vcs'' check_res.  do 2 eapply ex_intro. apply scan_res.
     do 2 eapply ex_intro. apply scan_res.
  clear scan_res.
  split; intro.
   (* -> *)
   destruct X. clear H1. destruct (H0 H) as [X [H1|H2]].
    (* this method was in the augmented specs' *)
    clear H0. destruct (mdesc_eq_dec (premethod_name, premethod_descriptor) mdesc).
     (* (premethod_name, premethod_descriptor) = mdesc *)
     split. assumption. right. split.
      (* this method wasnt in specs' *)
      unfold SpecTable.In. intros [spec' in_specs']. apply seen_specs in in_specs'. rewrite e in n. contradiction.
      split. rewrite <- e. assumption.
      (* but it was in the list *)
      exists m. split.
       (* this method is at the head of this list *)
       destruct mdesc. inversion e. unfold m. subst t d. apply C.has_premethod_cons_1.
       (* it has the right spec *)
       rewrite e in H1.
       assert (SpecTable.find mdesc (SpecTable.add mdesc (premethod_spec m) specs') = Some (premethod_spec m)).
        apply SpecTable.find_1. apply SpecTable.add_1. apply MethodDesc.eq_refl.
       rewrite (SpecTable.find_1 H1) in H0. inversion H0. split; reflexivity.
     (* (premethod_name, premethod_descriptor) <> mdesc *)
     split. assumption.
     left. eapply SpecTable.add_3. apply n0. apply H1.
    (* this method was in the rest of the list *)
    clear H0. split. assumption. right. destruct H2. destruct (not_In_add mdesc _ _ specs' H0). split.
     apply H3.
     destruct H1. split. intro in_seen. destruct H1. right. assumption.
     destruct H4. exists x. destruct H4. split.
      unfold m. destruct mdesc. apply C.has_premethod_cons_2.
       assumption. apply pair_neq. apply H2.
      assumption.
   (* <- *)
   destruct X. apply H1. clear H1 H0.
   destruct H as [X [H|H]].
    (* this mdesc was in specs' *)
    split. assumption. left. destruct (mdesc_eq_dec (premethod_name, premethod_descriptor) mdesc).
      subst mdesc. apply seen_specs in H. contradiction.
      apply SpecTable.add_2. apply n0. apply H.
    (* this mdesc wasn't in specs *)
    split. assumption. destruct H. destruct (mdesc_eq_dec (premethod_name, premethod_descriptor) mdesc).
     subst. left. destruct H0 as [_ [x H0]]. destruct H0. destruct H1. inversion H0; subst.
      apply SpecTable.add_1. apply MethodDesc.eq_refl.
      elimtype False. destruct H20; apply H2; reflexivity.
     right. split.
      unfold not. intros. destruct H1.
      assert (SpecTable.MapsTo mdesc x specs'). eapply SpecTable.add_3. apply n0. apply H1.
       apply H. exists x. apply H2.
      split.
       destruct H0. intro in_newseen.  destruct in_newseen; contradiction.
      destruct H0 as [_ [m' [has_m' m'_spec]]]. exists m'. inversion has_m'; subst.
       elimtype False. apply n0. reflexivity.
       auto.
Save.

Lemma scan_methods_ok2 : forall src class_annot m_list specs specs' vcs vcs',
 scan_methods src class_annot m_list nil specs (SpecTable.empty GA.method_specification) vcs = Val (specs', vcs') ->
 forall mdesc spec,
  SpecTable.MapsTo mdesc spec specs' <-> fst mdesc <> B.init /\ exists m, C.has_premethod m_list mdesc m /\ C.premethod_static m = false /\ premethod_spec m = spec.
intros. 
rewrite (scan_methods_ok2_aux src class_annot m_list nil specs (SpecTable.empty GA.method_specification) specs').
 rewrite SpecTableFacts.empty_mapsto_iff. rewrite SpecTableFacts.empty_in_iff. tauto.
 intros. rewrite SpecTableFacts.empty_mapsto_iff in H0. contradiction.
 intros. rewrite SpecTableFacts.empty_mapsto_iff in H0. contradiction.
 exists vcs. exists vcs'. assumption.
Save.

Section WithClasses.

Hypothesis preclasses : CP.Preclasspool.t.
Hypothesis classes : CP.cert_classpool.
Hypothesis classes_spec_table : ClassTable.t (SpecTable.t GA.method_specification).

(* specs in these functions should contain specs for the current class and 
   the super classes - any can implement the interface. *)
Definition check_interface_premethod (clsnm : B.Classname.t)
                                     (class_annot : GA.A.class_annotation)
                                     (specs : SpecTable.t GA.method_specification)
                                     (md : C.premethod)
                                     : error_monad vcset :=
 let thisspec := premethod_spec md in
 let mdesc := (C.premethod_name md, C.premethod_descriptor md) in
 match SpecTable.find mdesc specs with
 | None => fail (err_no_impl mlapp B.Methodname.to_string (C.premethod_name md))
 | Some spec => tagfailure (err_implementing_failure mlapp B.Methodname.to_string (C.premethod_name md) mlapp err_sep) (check_override (clsnm,C.premethod_name md) class_annot spec thisspec)
 end.

Lemma check_interface_premethod_ok : forall src class_annot specs md vcs,
  check_interface_premethod src class_annot specs md = Val vcs ->
  vcset_ok vcs ->
  exists implspec, SpecTable.find (C.premethod_name md, C.premethod_descriptor md) specs = Some implspec /\
  safe_override implspec (premethod_spec md).
Proof.
  intros.
  unfold check_interface_premethod in H.
  destruct (SpecTable.find (C.premethod_name md, C.premethod_descriptor md) specs).
    exists m.
    case_eq (check_override (src, C.premethod_name md) class_annot m (premethod_spec md)); intros.
      split; auto.
      apply (check_override_ok _ _ _ _ _ H1).
      rewrite H1 in H.
      simpl in H.
      injection H as Heq. subst v.
      assumption.

      rewrite H1 in H.
      discriminate.

    discriminate.
Qed.

Definition check_interface_method (clsnm : B.Classname.t)
                                  (class_annot : GA.A.class_annotation)
                                  (specs : SpecTable.t GA.method_specification)
                                  (mthd : (B.Methodname.t*C.descriptor)*C.method)
                                  : error_monad vcset :=
 let md := snd mthd in
 let thisspec := method_spec md in
 let mdesc := fst mthd in
 match SpecTable.find mdesc specs with
 | None => fail (err_no_impl mlapp B.Methodname.to_string (C.method_name md))
 | Some spec => tagfailure (err_implementing_failure mlapp B.Methodname.to_string (C.method_name md) mlapp err_sep) (check_override (clsnm,C.method_name md) class_annot spec thisspec)
 end.

Lemma check_interface_method_ok : forall src class_annot specs mkey md vcs,
  check_interface_method src class_annot specs (mkey,md) = Val vcs ->
  vcset_ok vcs ->
  exists implspec, SpecTable.find mkey specs = Some implspec /\
  safe_override implspec (method_spec md).
Proof.
  intros.
  unfold check_interface_method in H.
  simpl in H.
  destruct (SpecTable.find mkey specs).
    exists m.
    case_eq (check_override (src, C.method_name md) class_annot m (method_spec md)); intros; rewrite H1 in H.
      split; auto.
      apply (check_override_ok _ _ _ _ _ H1).
      injection H as Heq.
      subst v.
      assumption.

      discriminate.

    discriminate.
Qed.


Definition interfaces_checked (specs:SpecTable.t GA.method_specification) (iface:B.Classname.t) (vcs:vcset) := forall mth m_annot,
  PA.interface_reqs_method classes preclasses iface mth m_annot ->
  vcset_ok vcs ->
  exists implspec, SpecTable.find mth specs = Some implspec /\
    safe_override implspec m_annot.

Program Definition scan_interface_aux
  (clsnm : B.Classname.t)
  (class_annot : GA.A.class_annotation)
  (specs : SpecTable.t GA.method_specification)
  (f : forall i : B.Classname.t, error_monad {vcs:vcset | interfaces_checked specs i vcs})
  (iface : B.Classname.t)
  (pi : C.preclass | CP.Preclasspool.lookup preclasses iface = Some pi)
  : error_monad {vcs:vcset | interfaces_checked specs iface vcs} :=
  match CP.class_loaded_dec classes iface with
    | inleft (exist c _) =>
      if C.class_interface c then
        vcs1 <- check_vc (check_interface_method clsnm class_annot specs) (C.MethodList.elements (C.class_methods c)) vcset_empty;::
                (* Program doesn't produce an equality unless we expand f a bit *)
        vcs2 <- check_vc (fun x => r <- f x;: ret r) (C.class_interfaces c) vcset_empty;::
        ret (vcset_union vcs1 vcs2)

      else
        fail (err_class_should_be_interface mlapp err_sep mlapp (B.Classname.to_string iface))
    | inright _ =>
      if C.preclass_interface pi then
        vcs1 <- check_vc (check_interface_premethod clsnm class_annot specs) (C.preclass_methods pi) vcset_empty;::
                (* Program doesn't produce an equality unless we expand f a bit *)
        vcs2 <- check_vc (fun x => r <- f x;: ret r) (C.preclass_super_interfaces pi) vcset_empty;::
        ret (vcset_union vcs1 vcs2)
      else
        fail (err_class_should_be_interface mlapp err_sep mlapp (B.Classname.to_string iface))
  end.
Next Obligation.
  rename wildcard' into loaded.
  clear Heq_anonymous.
  rename Heq_anonymous0 into methods_ok. symmetry in methods_ok.
  rename Heq_anonymous1 into super_ifaces_ok. symmetry in super_ifaces_ok.

  intros mth m_annot iface_req vcs_ok.
  inversion iface_req; subst.
    rewrite (CP.class_loaded_unique H0 loaded) in *.
    apply C.MethodList.elements_1 in H1.
    destruct (check_vc_ok (mth,md) methods_ok) as [vcs' [check_ok vcs_ok']]. eauto using vcset_union_ok1. destruct ((proj1 (InA_alt _ _ _)) H1) as [[x1 x2] [xeq xin]]. unfold C.MethodList.eq_key_obj, C.MethodList.Key.eq in xeq. destruct xeq as [xeq1 xeq2]; simpl in *; subst x1 x2. assumption.
    eapply check_interface_method_ok; eauto.

    destruct (H0 c loaded).

    rewrite (CP.class_loaded_unique H0 loaded) in *.
    destruct (check_vc_ok iface' super_ifaces_ok) as [vcs' [check_ok vcs_ok']]. eauto using vcset_union_ok2. assumption.
    destruct_err (f iface') check_ok vcs vcseq.
    destruct vcs as [vcs0 vcs0ok].
    apply vcs0ok. assumption.
    simpl in *. injection check_ok as vcseq'. subst vcs0. assumption.

    destruct (H0 c loaded).
Qed.
Next Obligation.
  rename wildcard' into not_loaded.
  rename H into pi_exists.
  clear Heq_anonymous.
  rename Heq_anonymous0 into methods_ok. symmetry in methods_ok.
  rename Heq_anonymous1 into super_ifaces_ok. symmetry in super_ifaces_ok.

  intros mth m_annot iface_req vcs_ok.
  inversion iface_req; subst.
    destruct not_loaded. exists c. assumption.

    rewrite pi_exists in H0.
    injection H0 as H0'.
    subst pc.
    destruct (check_vc_ok mth0 methods_ok) as [vcs' [check_ok vcs_ok']]. eauto using vcset_union_ok1. apply C.has_premethod_in. assumption.
    eapply check_interface_premethod_ok; eauto.

    destruct not_loaded. exists c. assumption.

    rewrite pi_exists in H0.
    injection H0 as H0'.
    subst pc.
    destruct (check_vc_ok iface' super_ifaces_ok) as [vcs' [check_ok vcs_ok']]. eauto using vcset_union_ok2. assumption.
    destruct_err (f iface') check_ok vcs vcseq.
    destruct vcs as [vcs0 vcs0ok].
    apply vcs0ok. assumption.
    simpl in *. injection check_ok as vcseq'. subst vcs0. assumption.
Qed.

Definition scan_interface
  (clsnm : B.Classname.t)
  (class_annot : GA.A.class_annotation)
  (specs : SpecTable.t GA.method_specification)
  (iface : B.Classname.t)
  : error_monad {vcs:vcset | interfaces_checked specs iface vcs} :=
  CP.Preclasspool.chain_fix _ preclasses (fun k => fail (err_cycle mlapp (B.Classname.to_string k))) (fun k => fail (err_notfound mlapp (B.Classname.to_string k))) (scan_interface_aux clsnm class_annot specs) iface.

Record correct_specs (nm:B.Classname.t) (spec_table:SpecTable.t GA.method_specification) : Prop := mk_correct_specs
 { cspecs_not_init : forall md mspec,
   SpecTable.MapsTo md mspec spec_table -> fst md <> B.init
 ; cspecs_overriding: forall md mspec,
   SpecTable.MapsTo md mspec spec_table ->
   (forall nmS cS m, A.assignable classes (C.ty_obj nm) (C.ty_obj nmS) ->
                     CP.class_loaded classes nmS cS ->
                     C.class_interface cS = false ->
                     C.MethodList.lookup (C.class_methods cS) md = Some m ->
                     C.method_static m = false ->
                     safe_override mspec (method_spec m))
 ; cspecs_implementing: forall c iface ispec md,
    fst md <> B.init ->
    CP.class_loaded classes nm c ->
    PA.should_implement classes preclasses nm iface ->
    PA.interface_reqs_method classes preclasses iface md ispec ->
    exists mspec,
      SpecTable.MapsTo md mspec spec_table /\
      safe_override mspec ispec
 ; cspecs_exist : forall md m c,
    CP.class_loaded classes nm c ->
    fst md <> B.init ->
    C.MethodList.lookup (C.class_methods c) md = Some m ->
    C.method_static m = false ->
    SpecTable.MapsTo md (method_spec m) spec_table
 ; cspecs_exist_2 : forall md,
    fst md <> B.init ->
    (exists nmS, exists cS, exists m,
      A.assignable classes (C.ty_obj nm) (C.ty_obj nmS)
      /\ CP.class_loaded classes nmS cS
      /\ C.class_interface cS = false
      /\ C.MethodList.lookup (C.class_methods cS) md = Some m
      /\ C.method_static m = false) ->
    exists mspec, SpecTable.MapsTo md mspec spec_table
 ; cspecs_minimal : forall md mspec,
    SpecTable.MapsTo md mspec spec_table <->
    fst md <> B.init /\
    PA.minimal_methodspec classes preclasses nm md mspec
 }.

Record correct_specs_preclass (nm:B.Classname.t) (spec_table:SpecTable.t GA.method_specification) : Prop := mk_correct_specs_preclass
 { cspecsp_not_init : forall md mspec,
   SpecTable.MapsTo md mspec spec_table -> fst md <> B.init
 ; cspecsp_overriding_1: forall md mspec,
    SpecTable.MapsTo md mspec spec_table ->
    forall nmS cS m, PA.pc_cross_sub_class classes preclasses nm nmS ->
                     CP.class_loaded classes nmS cS ->
                     C.class_interface cS = false ->
                     C.MethodList.lookup (C.class_methods cS) md = Some m ->
                     C.method_static m = false ->
                     safe_override mspec (method_spec m)
 ; cspecsp_overriding_2: forall md mspec,
    SpecTable.MapsTo md mspec spec_table ->
    forall nmS pcS m, PA.pc_sub_class classes preclasses nm nmS ->
                      CP.Preclasspool.lookup preclasses nmS = Some pcS ->
                      C.preclass_interface pcS = false ->
                      C.has_premethod (C.preclass_methods pcS) md m ->
                      C.premethod_static m = false ->
                      safe_override mspec (premethod_spec m)
 ; cspecsp_implementing: forall pc iface ispec md,
    fst md <> B.init ->
    CP.Preclasspool.lookup preclasses nm = Some pc ->
    PA.should_implement classes preclasses nm iface ->
    PA.interface_reqs_method classes preclasses iface md ispec ->
    exists mspec,
      SpecTable.MapsTo md mspec spec_table /\
      safe_override mspec ispec
 ; cspecsp_exist : forall md m pc,
    CP.Preclasspool.lookup preclasses nm = Some pc ->
    fst md <> B.init ->
    C.has_premethod (C.preclass_methods pc) md m ->
    C.premethod_static m = false ->
    SpecTable.MapsTo md (premethod_spec m) spec_table
 ; cspecsp_exist_2 : forall md,
    fst md <> B.init ->
    (exists nmS, exists cS, exists m,
                      PA.pc_cross_sub_class classes preclasses nm nmS /\
                      CP.class_loaded classes nmS cS /\
                      C.class_interface cS = false /\
                      C.MethodList.lookup (C.class_methods cS) md = Some m /\
                      C.method_static m = false)
    \/
    (exists nmS, exists pcS, exists m,
                       PA.pc_sub_class classes preclasses nm nmS /\
                       CP.Preclasspool.lookup preclasses nmS = Some pcS /\
                       C.preclass_interface pcS = false /\
                       C.has_premethod (C.preclass_methods pcS) md m /\
                       C.premethod_static m = false) ->
    exists mspec, SpecTable.MapsTo md mspec spec_table
 ; cspecsp_minimal : forall md mspec,
    SpecTable.MapsTo md mspec spec_table <->
    fst md <> B.init /\
    PA.minimal_methodspec classes preclasses nm md mspec
 }.

Lemma MapsTo_functional : forall x e e' (m:SpecTable.t GA.method_specification),
 SpecTable.MapsTo x e m ->
 SpecTable.MapsTo x e' m ->
 e = e'.
intros. 
assert (SpecTable.find x m = Some e). apply SpecTable.find_1. assumption.
rewrite (SpecTable.find_1 H0) in H1. inversion H1. reflexivity.
Save.

Lemma one_premethod_safe_override : forall l mdesc m specs,
 C.has_premethod l mdesc m ->
 every (premethod_safe_override specs) l ->
 premethod_safe_override specs m.
intros l mdesc m specs l_has_m all_l_good.
induction l as [|a l].
 inversion l_has_m.
 inversion l_has_m; subst.
  inversion all_l_good. apply H1.
  apply IHl. assumption. inversion all_l_good. assumption.
Save.

Lemma has_premethod_names : forall l md m,
 C.has_premethod l md m ->
 md = (C.premethod_name m, C.premethod_descriptor m).
induction l; intros; inversion H; intuition eauto.
Save.

Lemma correct_specs_step_from_classes_to_preclasses : forall nmS spec_table_super pc spec_table_current nm c,
 correct_specs nmS spec_table_super ->
 CP.class_loaded classes nmS c ->
 (forall c', ~CP.class_loaded classes nm c') ->
 CP.Preclasspool.lookup preclasses nm = Some pc ->
 C.preclass_super_name pc = Some nmS ->
 C.preclass_interface pc = false ->
 every (premethod_safe_override spec_table_super) (C.preclass_methods pc) ->
 (forall iface md ispec, fst md <> B.init -> PA.should_implement classes preclasses nm iface -> PA.interface_reqs_method classes preclasses iface md ispec -> exists mspec, SpecTable.MapsTo md mspec (STOverlay.overlay _ spec_table_current spec_table_super) /\ safe_override mspec ispec) ->
 (forall mdesc spec, SpecTable.MapsTo mdesc spec spec_table_current  <-> fst mdesc <> B.init /\ exists m, C.has_premethod (C.preclass_methods pc) mdesc m /\ C.premethod_static m = false /\ premethod_spec m = spec) ->
 correct_specs_preclass nm (STOverlay.overlay _ spec_table_current spec_table_super).
Proof.
intros nmS spec_table_super pc spec_table_current nm c.
intros spec_table_super_correct S_loaded nm_notloaded nm_exists pc_S notint all_overrides_correct all_implemented all_exist.
assert (none_init:forall md mspec, SpecTable.MapsTo md mspec (STOverlay.overlay GA.method_specification spec_table_current spec_table_super) -> fst md <> B.init).
 intros. rewrite STOverlay.overlay_law in H. destruct H as [H|[X1 X2]].
  rewrite all_exist in H. tauto.
  eauto using cspecs_not_init.
constructor; intros.
 (* cspecsp_not_init *)
 eauto.
 (* cspecsp_overriding_1 *)
 rewrite STOverlay.overlay_law in H. 
 assert (A.assignable classes (C.ty_obj nmS) (C.ty_obj nmS0)) by (eapply PA.cross_assignable_undo_step_2; eauto; apply nm_exists).
 destruct H as [H|H].
  (* in spec_table_current *)
  set (H_copy := H). revert H_copy. intro H_copy.
  rewrite all_exist in H. 
  destruct H as [neq_init [m' [has_m' [m'_static m'_mspec]]]].
  destruct (cspecs_exist_2 _ _ spec_table_super_correct md).
   assumption.
   intuition eauto 8.
  destruct (one_premethod_safe_override _ _ _ _ has_m' all_overrides_correct) as [called_init|[static|[not_called_init [X1|X2]]]].
   (* this method is called init : impossible *)
   rewrite <- called_init in neq_init. rewrite (has_premethod_names _ _ _ has_m') in neq_init. elimtype False. apply neq_init. reflexivity.
   (* this method is static : impossible *)
   rewrite m'_static in static. discriminate.
   (* this method is not in spec_table_super: impossible *)
   elimtype False. apply X1. rewrite <- (has_premethod_names _ _ _ has_m'). exists x. assumption.
   (* this method was in spec_table_super *)
   rewrite <- m'_mspec. eapply safe_override_trans.
    apply X2. rewrite <- (has_premethod_names _ _ _ has_m'). eassumption.
    eapply (cspecs_overriding _ _ spec_table_super_correct md x); eauto.
  (* not in spec_table_current *)
  destruct H as [X1 X2].
  eapply (cspecs_overriding _ _ spec_table_super_correct md mspec X2); eauto.
 (* cspecsp_overriding_2 *)
 assert (nm = nmS0) by (eapply PA.pre_assignable_barrier; eauto).
 subst.
 assert (mspec = premethod_spec m).
  eapply MapsTo_functional. apply H. rewrite STOverlay.overlay_law. left. rewrite all_exist. split.
   eapply none_init. apply H.
   exists m. intuition congruence.
 subst. apply safe_override_refl.
 (* cspecsp_implementing *)
 apply all_implemented with (iface:=iface) (md:=md); auto.
 (* cspecsp_exist *)
 rewrite STOverlay.overlay_law. left. rewrite all_exist. split. assumption. exists m. intuition congruence.
 (* cspecsp_exist_2 *)
 destruct H0 as [[nmS' [cS' [m [nm_S' [S'_loaded [S'_not_interface S'_has_m]]]]]]
               |[nmS' [pcS' [m [nm_S' [S'_exists [S'_not_interface S'_has_m]]]]]]].
  (* case 1 *)
  destruct (option_informative (SpecTable.find md spec_table_current)) as [[mspec find_res] | find_res].
   exists mspec. rewrite STOverlay.overlay_law. left. apply SpecTable.find_2. apply find_res.
   destruct (cspecs_exist_2 _ _ spec_table_super_correct md).
    assumption. exists nmS'. exists cS'. exists m. intuition. eapply PA.cross_assignable_undo_step_2; eauto.
   exists x. rewrite STOverlay.overlay_law. right. split. 
    apply find_None_is_not_In. assumption.
    assumption.
  (* case 2 *)
  assert (nm = nmS'). eapply PA.pre_assignable_barrier; eauto.
  subst.
  exists (premethod_spec m). rewrite STOverlay.overlay_law. left. rewrite all_exist. split. assumption. exists m. intuition congruence.
 (* cspecsp_minimal *)
  split.
  intro. destruct (STOverlay.overlay_law1 _ _ _ _ _ H) as [maps|[notin maps]].
   destruct (proj1 (all_exist _ _) maps) as [notinit [m [pm [ps pa]]]]. split. assumption. apply PA.minimal_methodspec_pre with (pc:=pc) (m:=m); auto.
   split. eapply none_init; eauto.
   eapply PA.minimal_methodspec_prestep with (pc:=pc) (nmS:=nmS); auto.
    (* show that any method matching md must be static (and hence ignored). *)
    intros m' hasprem. case_eq (C.premethod_static m'). auto. intro notstatic. destruct notin. exists (premethod_spec m'). apply (proj2 (all_exist md (premethod_spec m'))).
     split. eapply none_init; eauto. exists m'. split. assumption. split. assumption. reflexivity.
    apply (proj2 (proj1 (cspecs_minimal _ _ spec_table_super_correct md mspec) maps)).
  intros [notinit mmspec].  inversion mmspec as [pc' m _ nm_exists' | |pc' nm' _ nm_exists' only_static super'].
   apply STOverlay.overlay_law2. left. eapply (proj2 (all_exist md mspec)). rewrite nm_exists in nm_exists'. injection nm_exists' as pceq. subst pc'. eauto.
   destruct (nm_notloaded c0 H).
   apply STOverlay.overlay_law2. right. rewrite nm_exists in nm_exists'. injection nm_exists' as pceq. subst pc'. split.
    intros [spec' specentry]. destruct (proj1 (all_exist _ _) specentry) as [_ [m [has_m [m_static _]]]]. rewrite (only_static m has_m) in m_static. discriminate.
    apply (proj2 (cspecs_minimal _ _ spec_table_super_correct md mspec)). rewrite pc_S in super'. injection super' as supereq. subst nm'. auto.
Save.

Lemma correct_specs_step_within_preclasses : forall nmS spec_table_super pc spec_table_current nm,
 correct_specs_preclass nmS spec_table_super ->
 (forall c, ~CP.class_loaded classes nmS c) ->
 (forall c, ~CP.class_loaded classes nm c) ->
 CP.Preclasspool.lookup preclasses nm = Some pc ->
 C.preclass_super_name pc = Some nmS ->
 C.preclass_interface pc = false ->
 every (premethod_safe_override spec_table_super) (C.preclass_methods pc) ->
 (forall iface md ispec, fst md <> B.init -> PA.should_implement classes preclasses nm iface -> PA.interface_reqs_method classes preclasses iface md ispec -> exists mspec, SpecTable.MapsTo md mspec (STOverlay.overlay _ spec_table_current spec_table_super) /\ safe_override mspec ispec) ->
 (forall mdesc spec, SpecTable.MapsTo mdesc spec spec_table_current  <-> fst mdesc <> B.init /\ exists m, C.has_premethod (C.preclass_methods pc) mdesc m /\ C.premethod_static m = false /\ premethod_spec m = spec) ->
 correct_specs_preclass nm (STOverlay.overlay _ spec_table_current spec_table_super).
Proof.
intros nmS spec_table_super pc spec_table_current nm.
intros spec_table_super_correct S_not_loaded nm_not_loaded nm_exists pc_S notint all_overrides_correct all_implemented all_exist.
assert (none_init:forall md mspec, SpecTable.MapsTo md mspec (STOverlay.overlay GA.method_specification spec_table_current spec_table_super) -> fst md <> B.init).
 intros. rewrite STOverlay.overlay_law in H. destruct H as [X|[X1 X2]].
  rewrite all_exist in X. tauto.
  eauto using cspecsp_not_init.
constructor; intros.
 (* cspecsp_not_init *)
 eauto.
 (* cspecsp_overriding_1 *)
 assert (PA.pc_cross_sub_class classes preclasses nmS nmS0).
  eapply PA.cross_assignable_undo_step; eauto.
 destruct (C.has_premethod_dec (C.preclass_methods pc) md) as [[m' pc_has_m'] | no_m'].
  (* The method is in the current class *)
  case_eq (C.premethod_static m').
   (* But it's static, so doesn't count. *)
   intro static_m'.
   assert (current_has_no_md:~SpecTable.In md spec_table_current).
    unfold not. intro. destruct H6. rewrite all_exist in H6. destruct H6 as [_ [m'' [has_m'' [X _]]]]. rewrite (C.has_premethod_functional _ _ _ _ pc_has_m' has_m'') in *. rewrite X in static_m'. discriminate.
   assert (super_has_md:SpecTable.MapsTo md mspec spec_table_super).
    rewrite STOverlay.overlay_law in H. destruct H.
     elimtype False. apply current_has_no_md. exists mspec. apply H.
     destruct H. apply H6.
   eapply (cspecsp_overriding_1 _  _ spec_table_super_correct); eauto.
  (* This is an instance method. *)
  intro static_m'.
  assert (current_has_md:SpecTable.MapsTo md (premethod_spec m') spec_table_current).
   rewrite all_exist. split. eauto. exists m'. intuition.
  assert (mspec = premethod_spec m').
   eapply MapsTo_functional. apply H. rewrite STOverlay.overlay_law. left. assumption.
  subst.
  destruct (cspecsp_exist_2 _ _ spec_table_super_correct md).
   eauto.
   intuition eauto 8.
  destruct (one_premethod_safe_override _ _ _ _ pc_has_m' all_overrides_correct) as [called_init|[static|[not_called_init [X|X]]]].
   (* method was called init: a lie *)
   elimtype False. refine (none_init md (premethod_spec m') _ _). rewrite STOverlay.overlay_law. left. assumption. rewrite (has_premethod_names _ _ _ pc_has_m'). assumption.
   (* method was static: a lie *)
   rewrite static_m' in static. discriminate.
   (* method wasn't in spec_table_super : a lie *)
   rewrite <- (has_premethod_names _ _ _ pc_has_m') in X. elimtype False. apply X. exists x. assumption.
   (* method was in spec_table_super *)
   rewrite <- (has_premethod_names _ _ _ pc_has_m') in X.
   eapply safe_override_trans.
    apply X. apply H6.
    eapply (cspecsp_overriding_1  _ _ spec_table_super_correct); eauto.
  (* method not in the current class *)
  assert (current_has_no_md:~SpecTable.In md spec_table_current).
   unfold not. intro. destruct H6. rewrite all_exist in H6. destruct H6 as [_ [m' [X _]]]. apply (no_m' _ X).
  assert (super_has_md:SpecTable.MapsTo md mspec spec_table_super).
   rewrite STOverlay.overlay_law in H. destruct H.
    elimtype False. apply current_has_no_md. exists mspec. apply H.
    destruct H. apply H6.
  eapply (cspecsp_overriding_1 _  _ spec_table_super_correct); eauto.
 (* cspecsp_overriding_2 *)  
 destruct (B.Classname.eq_dec nm nmS0).
  (* same as the current class *)
  subst. rewrite nm_exists in H1. inversion H1. subst. clear H1.
  assert (SpecTable.MapsTo md (premethod_spec m) spec_table_current).
   rewrite all_exist. split. eauto. exists m. eauto.
  replace mspec with (premethod_spec m).
   apply safe_override_refl.
   rewrite STOverlay.overlay_law in H. destruct H.
    eapply MapsTo_functional; eauto.
    destruct H. elimtype False. apply H. exists (premethod_spec m). apply H1.
  (* different class *)
  assert (PA.pc_sub_class classes preclasses nmS nmS0).
   eapply PA.pre_assignable_undo_step; eauto.
  (* FIXME: the following is almost exactly the same as the case for cspecsp_overriding_1 *)
  destruct (C.has_premethod_dec (C.preclass_methods pc) md) as [[m' pc_has_m'] | no_m'].
   (* The method is in the current class *)
  case_eq (C.premethod_static m').
   (* But it's static, so doesn't count. *)
   intro static_m'.
   assert (current_has_no_md:~SpecTable.In md spec_table_current).
    unfold not. intro. destruct H6. rewrite all_exist in H6. destruct H6 as [_ [m'' [has_m'' [X _]]]]. rewrite (C.has_premethod_functional _ _ _ _ pc_has_m' has_m'') in *. rewrite X in static_m'. discriminate.
   assert (super_has_md:SpecTable.MapsTo md mspec spec_table_super).
    rewrite STOverlay.overlay_law in H. destruct H.
     elimtype False. apply current_has_no_md. exists mspec. apply H.
     destruct H. apply H6.
   eapply (cspecsp_overriding_2 _  _ spec_table_super_correct); eauto.
  (* This is an instance method. *)
  intro static_m'.
   assert (current_has_md:SpecTable.MapsTo md (premethod_spec m') spec_table_current).
    rewrite all_exist. split. eauto. exists m'. intuition.
   assert (mspec = premethod_spec m').
    eapply MapsTo_functional. apply H. rewrite STOverlay.overlay_law. left. assumption.
   subst.
   destruct (cspecsp_exist_2 _ _ spec_table_super_correct md).
    eauto.
    intuition eauto 8.
   destruct (one_premethod_safe_override _ _ _ _ pc_has_m' all_overrides_correct) as [called_init|[static|[not_called_init [X|X]]]].
    (* method was called init : a lie *)
    elimtype False. refine (none_init md (premethod_spec m') _ _). rewrite STOverlay.overlay_law. left. assumption. rewrite (has_premethod_names _ _ _ pc_has_m'). assumption.    
    (* method was static: a lie *)
    rewrite static_m' in static. discriminate.
    (* method wasn't in spec_table_super : a lie *)
    rewrite <- (has_premethod_names _ _ _ pc_has_m') in X. elimtype False. apply X. exists x. assumption.
    (* method was in spec_table_super *)
    rewrite <- (has_premethod_names _ _ _ pc_has_m') in X.
    eapply safe_override_trans.
     apply X. apply H6.
     eapply (cspecsp_overriding_2 _ _ spec_table_super_correct); eauto.
   (* method not in the current class *)
   assert (current_has_no_md:~SpecTable.In md spec_table_current).
    unfold not. intro. destruct H6. rewrite all_exist in H6. destruct H6 as [_ [m'' [X _]]]. apply (no_m' _ X).
   assert (super_has_md:SpecTable.MapsTo md mspec spec_table_super).
    rewrite STOverlay.overlay_law in H. destruct H.
     elimtype False. apply current_has_no_md. exists mspec. apply H.
     destruct H. apply H6.
   eapply (cspecsp_overriding_2 _ _ spec_table_super_correct); eauto.
 (* cspecsp_implementing *)
 apply all_implemented with (iface:=iface) (md:=md); auto.
 (* cspecs_exists *)
 rewrite STOverlay.overlay_law. left. rewrite all_exist. split. eauto. exists m. intuition congruence.
 (* cspecs_exists_2 *)
 destruct H0 as [[nmS' [cS' [m [nm_S' [S'_loaded [S'_not_interface S'_has_m]]]]]]
               |[nmS' [pcS' [m [nm_S' [S'_exists [S'_not_interface S'_has_m]]]]]]].
  (* case 1 *)
  destruct (option_informative (SpecTable.find md spec_table_current)) as [[mspec find_res] | find_res].
   exists mspec. rewrite STOverlay.overlay_law. left. apply SpecTable.find_2. apply find_res.
   destruct (cspecsp_exist_2 _ _ spec_table_super_correct md).
    eauto. left. exists nmS'. exists cS'. exists m. intuition. eapply PA.cross_assignable_undo_step; eauto.
   exists x. rewrite STOverlay.overlay_law. right. split. 
    apply find_None_is_not_In. assumption.
    assumption.
  (* case 2 *)
  destruct (B.Classname.eq_dec nm nmS').
   (* talking about this class *)
   subst. exists (premethod_spec m). rewrite STOverlay.overlay_law. left. rewrite all_exist. split. eauto. exists m. intuition congruence.
   (* taling about a super class *)
   destruct (option_informative (SpecTable.find md spec_table_current)) as [[mspec find_res] | find_res].
    exists mspec. rewrite STOverlay.overlay_law. left. apply SpecTable.find_2. apply find_res.
    destruct (cspecsp_exist_2 _ _ spec_table_super_correct md).
     assumption. right. exists nmS'. exists pcS'. exists m. intuition. eapply PA.pre_assignable_undo_step; eauto.
    exists x. rewrite STOverlay.overlay_law. right. split. 
     apply find_None_is_not_In. assumption.
     assumption.
 (* cspecsp_minimal *)
  split.
  intro. destruct (STOverlay.overlay_law1 _ _ _ _ _ H) as [maps|[notin maps]].
   destruct (proj1 (all_exist _ _) maps) as [notinit [m [pm [ps pa]]]]. split. assumption. apply PA.minimal_methodspec_pre with (pc:=pc) (m:=m); auto.
   split. eapply none_init; eauto.
   eapply PA.minimal_methodspec_prestep with (pc:=pc) (nmS:=nmS); auto.
    intros m' hasprem. case_eq (C.premethod_static m'). auto. intro notstatic. destruct notin. exists (premethod_spec m'). apply (proj2 (all_exist md (premethod_spec m'))).
     split. eapply none_init; eauto. exists m'. split. assumption. split. assumption. reflexivity.
    apply (proj2 (proj1 (cspecsp_minimal _ _ spec_table_super_correct md mspec) maps)).
  intros [notinit mmspec].  inversion mmspec as [pc' m _ nm_exists' | |pc' nm' _ nm_exists' only_static super'].
   apply STOverlay.overlay_law2. left. eapply (proj2 (all_exist md mspec)). rewrite nm_exists in nm_exists'. injection nm_exists' as pceq. subst pc'. eauto.
   destruct (nm_not_loaded c H).
   apply STOverlay.overlay_law2. right. rewrite nm_exists in nm_exists'. injection nm_exists' as pceq. subst pc'. split.
    intros [spec' specentry]. destruct (proj1 (all_exist _ _) specentry) as [_ [m [has_m [m_static _]]]]. rewrite (only_static m has_m) in m_static. discriminate.
    apply (proj2 (cspecsp_minimal _ _ spec_table_super_correct md mspec)). rewrite pc_S in super'. injection super' as supereq. subst nm'. auto.
Save.

Definition checked_class (nm:B.Classname.t) (specs:SpecTable.t GA.method_specification) :=
   (exists c, CP.class_loaded classes nm c /\ correct_specs nm specs /\ C.class_interface c = false)
 \/(exists pc, CP.Preclasspool.lookup preclasses nm = Some pc
             /\correct_specs_preclass nm specs
             /\(forall c, ~CP.class_loaded classes nm c)
             /\C.preclass_interface pc = false).

Hypothesis classes_spec_table_correct : forall nm c,
 CP.class_loaded classes nm c ->
 C.class_interface c = false ->
 exists spec_table, ClassTable.MapsTo nm spec_table classes_spec_table /\ correct_specs nm spec_table.

(* coq gets upsets and chews huge amounts of CPU if you leave this inline... *)
Definition check_preclass_interfaces (pc:C.preclass) (spec_table_new:SpecTable.t GA.method_specification) : error_monad vcset :=
  check_vc (fun i => r <- (scan_interface (C.preclass_name pc) (C.preclass_annotation pc) spec_table_new i);: ret (proj1_sig r)) (C.preclass_super_interfaces pc) vcset_empty.

Program Definition check_preclass_aux
  (f:(forall nm:B.Classname.t, error_monad {vcs : vcset & {specs:SpecTable.t GA.method_specification | vcset_ok vcs -> checked_class nm specs}}))
  (nm:B.Classname.t) (pc:C.preclass | CP.Preclasspool.lookup preclasses nm = Some pc)
    : error_monad ({vcs : vcset & {specs:SpecTable.t GA.method_specification | vcset_ok vcs -> checked_class nm specs}}) :=
    (tagfailure ((B.Classname.to_string nm) mlapp err_sep)
      (match CP.class_loaded_dec classes nm with
         | inleft (exist c _) =>
           match C.class_interface c with
             | true => fail err_class_should_not_be_interface
             | false =>
               specs <- tagoptfail err_no_spec_found_for_class (ClassTable.find nm classes_spec_table);::
               ret (existT _ vcset_empty (exist _ specs _))
           end
         | inright _ =>
           match C.preclass_interface pc with true => fail err_class_should_not_be_interface | false => ret tt end;;;
           nmS <- tagoptfail err_preclass_should_have_superclass (C.preclass_super_name pc);::
           spec_table_super_vcs1 <- f nmS;::
           match spec_table_super_vcs1 with (existT vcs1 (exist spec_table_super _)) =>
             spec_table_current_vcs2 <- scan_methods nm (C.preclass_annotation pc) (C.preclass_methods pc) nil spec_table_super (SpecTable.empty _) vcset_empty;::
             match spec_table_current_vcs2 with (spec_table_current, vcs2) =>
               let spec_table_new := STOverlay.overlay _ spec_table_current spec_table_super in
               vcs3 <- check_preclass_interfaces pc spec_table_new;::
               Val (existT _ (vcset_union vcs1 (vcset_union vcs2 vcs3)) (exist _ spec_table_new _))
             end
           end
         end)).
Next Obligation.
 (* nm is in classes *)
 left. exists c. 
  symmetry in Heq_anonymous0. destruct (classes_spec_table_correct _ _ wildcard' Heq_anonymous0) as [specs' [specs'_lookup specs'_correct]].
  assert (specs' = specs). rewrite (ClassTable.find_1 specs'_lookup) in Heq_anonymous1. simpl in Heq_anonymous1. congruence.
  subst. intuition.
Qed.
Next Obligation.
 (* nm is not in classes *)
 (* clean up context. *)
 destruct wildcard'0. (* unit *)
 rename wildcard' into no_nm_class. clear Heq_anonymous.
 destruct (BoolExt.bool_dec (C.preclass_interface pc)) as [pc_interface|pc_interface]; [rewrite pc_interface in Heq_anonymous0; discriminate|clear Heq_anonymous0].
 clear Heq_anonymous2.
 rename Heq_anonymous3 into methods_checked.
 rename Heq_anonymous4 into interfaces_implemented.
 rename H0 into pc_exists.
(* inversion Heq_spec_table_current_vcs2. subst t v.*)
 rename H into vcs_ok.
 rename H1 into super_checked.
 rename spec_table_super_vcs1 into vcs1.
 rename X into spec_table_super.
 rename t into spec_table_current.
 rename v into vcs2.
(* rename wildcard'1 into super_checked.*)

 assert (nm_not_loaded:forall c, ~CP.class_loaded classes nm c) by (unfold not; intros; apply no_nm_class; exists c; assumption).
 (* but it is in the preclasses *)
 right. exists pc.
 destruct (OptionExt.option_dec (C.preclass_super_name pc)) as [[super_name super_name_res]|super_name_res]; rewrite super_name_res in Heq_anonymous1; try discriminate.
 simpl in Heq_anonymous1. injection Heq_anonymous1. intro.  subst super_name. clear Heq_anonymous1.

 assert (every (premethod_safe_override spec_table_super) (C.preclass_methods pc)). eapply scan_methods_ok. symmetry. eassumption. eapply vcset_union_ok1. eapply vcset_union_ok2. eassumption.
 assert (forall mdesc spec, SpecTable.MapsTo mdesc spec spec_table_current  <-> fst mdesc <> B.init /\ exists m, C.has_premethod (C.preclass_methods pc) mdesc m /\ C.premethod_static m = false /\ premethod_spec m = spec).
  intros. eapply scan_methods_ok2. symmetry. eassumption.

 destruct super_checked as [[c [c_loaded [super_specs_correct c_not_interface]]]
                           |[pcS [pcS_exists [super_specs_correct [not_loaded not_interface]]]]].
  eauto using vcset_union_ok1.
  (* super class was loaded *)
  assert (forall (super_specs_correct:correct_specs nmS spec_table_super) iface ispec md, fst md <> B.init -> PA.should_implement classes preclasses nm iface -> PA.interface_reqs_method classes preclasses iface md ispec -> exists mspec, SpecTable.MapsTo md mspec (STOverlay.overlay _ spec_table_current spec_table_super) /\ safe_override mspec ispec).
   intros until md. intros md_notinit iface_in i_meth.
   (* Where did the interface requirement come from? *)
   destruct (In_dec B.Classname.eq_dec iface (C.preclass_super_interfaces pc)).
     unfold check_preclass_interfaces in interfaces_implemented.
     symmetry in interfaces_implemented.
     destruct (check_vc_ok iface interfaces_implemented) as [vcs0 [iface_check vcs0_ok]]. eauto using vcset_union_ok2. assumption.
     destruct (scan_interface (C.preclass_name pc) (C.preclass_annotation pc) (STOverlay.overlay GA.method_specification spec_table_current spec_table_super) iface) as [[vcs iface_ok]|]; [|discriminate].
     destruct (iface_ok _ _ i_meth) as [mspec' [mspecfound mspecok]]. simpl in *. injection iface_check as vcseq. subst vcs. assumption.
     exists mspec'. auto using SpecTable.find_2.

     pose (PA.does_not_implement _ _ _ _ _ _ pc_exists nm_not_loaded iface_in n super_name_res).
     destruct super_specs_correct.
     (* Does the spec table entry come from the current class or the super class? *)
     destruct (C.has_premethod_dec (C.preclass_methods pc) md) as [[pm has_pm]|no_pm].
       case_eq (C.premethod_static pm); intro.
         destruct (cspecs_implementing0 c iface ispec md); auto.
         exists x. split. apply STOverlay.overlay_law2. right. split.
           intro md_in.
           destruct md_in as [spec' md_in].
           destruct (proj1 (H0 _ _) md_in) as [_ [pm' [has_pm' [notstatic_pm' _]]]].
           rewrite (C.has_premethod_functional _ _ _ _ has_pm has_pm') in *.
           rewrite notstatic_pm' in *.
           discriminate.

           tauto. tauto.

          exists (premethod_spec pm). split.
            apply (STOverlay.overlay_law2). left.  apply (proj2 (H0 md (premethod_spec pm))).
            split. assumption.
            exists pm. intuition auto.
            destruct (cspecs_implementing0 c iface ispec md) as [mspec [super_spec super_spec_ok]]; auto.
            eapply safe_override_trans with (s2:=mspec).
              apply one_premethod_safe_override with (mdesc:=md) (m:=pm) in H; auto.
              inversion H. destruct md_notinit. rewrite (C.has_premethod_name has_pm). rewrite H2. reflexivity.
              destruct H2 as [static|[_ [not_in_super|super_safe]]].
                rewrite H1 in static.
                discriminate.

                destruct not_in_super.
                exists mspec.
                rewrite <- (C.has_premethod_name has_pm).
                assumption.
              apply super_safe.
                rewrite <- (C.has_premethod_name has_pm).
                assumption.

              assumption.
        (* Inherited from a super class *)      
        destruct (cspecs_implementing0 c iface ispec md); eauto.
        exists x.
        split. apply STOverlay.overlay_law2. right. split.
          intro in_current.
          destruct in_current as [mspec in_current].
          destruct (proj1 (H0 _ _) in_current) as [_ [pm [has_pm _]]].
          apply (no_pm pm has_pm).

          tauto. tauto.

   eauto 6 using correct_specs_step_from_classes_to_preclasses.

   (* super class was in preclasses *)
   (* FIXME: This interfaces stuff is *very* similar to the one above, try to reconcile them. *)
   assert (forall iface ispec md, fst md <> B.init -> PA.should_implement classes preclasses nm iface -> PA.interface_reqs_method classes preclasses iface md ispec -> exists mspec, SpecTable.MapsTo md mspec (STOverlay.overlay _ spec_table_current spec_table_super) /\ safe_override mspec ispec).
    intros until md. intros md_notinit iface_in i_meth.
     (* Where did the interface requirement come from? *)
     destruct (In_dec B.Classname.eq_dec iface (C.preclass_super_interfaces pc)).
      unfold check_preclass_interfaces in interfaces_implemented.
      symmetry in interfaces_implemented.
      destruct (check_vc_ok iface interfaces_implemented) as [vcs0 [iface_check vcs0_ok]]. eauto using vcset_union_ok2. assumption.
      destruct (scan_interface (C.preclass_name pc) (C.preclass_annotation pc) (STOverlay.overlay GA.method_specification spec_table_current spec_table_super) iface) as [[vcs' iface_ok]|]; [|discriminate].
      destruct (iface_ok _ _ i_meth) as [mspec' [mspecfound mspecok]]. simpl in iface_check. injection iface_check as vcseq. subst vcs0. assumption.
      exists mspec'. auto using SpecTable.find_2.

      pose (PA.does_not_implement _ _ _ _ _ _ pc_exists nm_not_loaded iface_in n super_name_res).
      destruct super_specs_correct.
      (* Does the spec table entry come from the current class or the super class? *)
      destruct (C.has_premethod_dec (C.preclass_methods pc) md) as [[pm has_pm]|no_pm].
        case_eq (C.premethod_static pm); intro.
          destruct (cspecsp_implementing0 pcS iface ispec md); auto.
          exists x. split. apply STOverlay.overlay_law2. right. split.
            intro md_in.
            destruct md_in as [spec' md_in].
            destruct (proj1 (H0 _ _) md_in) as [_ [pm' [has_pm' [notstatic_pm' _]]]].
            rewrite (C.has_premethod_functional _ _ _ _ has_pm has_pm') in *.
            rewrite notstatic_pm' in *.
            discriminate.

            tauto. tauto.

          exists (premethod_spec pm). split.
            apply (STOverlay.overlay_law2). left.  apply (proj2 (H0 md (premethod_spec pm))).
            split. assumption.
            exists pm. intuition auto.
            destruct (cspecsp_implementing0 pcS iface ispec md) as [mspec [super_spec super_spec_ok]]; auto.
            eapply safe_override_trans with (s2:=mspec).
              apply one_premethod_safe_override with (mdesc:=md) (m:=pm) in H; auto.
              inversion H. destruct md_notinit. rewrite (C.has_premethod_name has_pm). rewrite H2. reflexivity.
              destruct H2 as [static|[_ [not_in_super|super_safe]]].
                rewrite H1 in static.
                discriminate.

                destruct not_in_super.
                exists mspec.
                rewrite <- (C.has_premethod_name has_pm).
                assumption.
              apply super_safe.
                rewrite <- (C.has_premethod_name has_pm).
                assumption.

              assumption.
        (* Inherited from a super class *)      
        destruct (cspecsp_implementing0 pcS iface ispec md); eauto.
        exists x.
        split. apply STOverlay.overlay_law2. right. split.
          intro in_current.
          destruct in_current as [mspec in_current].
          destruct (proj1 (H0 _ _) in_current) as [_ [pm [has_pm _]]].
          apply (no_pm pm has_pm).

          tauto. tauto.

   eauto 6 using correct_specs_step_within_preclasses.
Qed.

Definition check_preclass' := CP.Preclasspool.chain_fix _ preclasses (fun k => fail (err_cycle mlapp (B.Classname.to_string k))) (fun k => fail (err_notfound mlapp (B.Classname.to_string k))) check_preclass_aux.


Definition check_preclass (k:B.Classname.t) : error_monad (vcset * SpecTable.t GA.method_specification)
 :=
  match CP.Preclasspool.lookup preclasses k with
    | None => fail (err_notfound mlapp (B.Classname.to_string k))
    | Some pc =>
      match C.preclass_interface pc with
        | true  => ret (vcset_empty, (SpecTable.empty _))
        | false =>
          r <- check_preclass' k;:
          match r with
            | (existT vcs (exist specs _)) => ret (vcs, specs)
          end
      end
  end.

(* Cut down version of the one in ResourceLogic *)
Record preclass_verified_overrides (pc : C.preclass)
                       : Prop :=
 { preclass_verified_overrides_classes1 :
                               forall cB nmB mA mB md,
                                 fst md <> B.init ->
                                 C.preclass_interface pc = false ->
                                 CP.class_loaded classes nmB cB ->
                                 PA.pc_cross_sub_class classes preclasses (C.preclass_name pc) nmB ->
                                 C.class_interface cB = false ->
                                 C.has_premethod (C.preclass_methods pc) md mA ->
                                 C.MethodList.lookup (C.class_methods cB) md = Some mB ->
                                 C.premethod_static mA = false ->
                                 C.method_static mB = false ->
                                 safe_override (premethod_spec mA) (method_spec mB)
 ; preclass_verified_overrides_classes2 :
                               forall cB nmB mA mB md,
                                 fst md <> B.init ->
                                 C.preclass_interface pc = false ->
                                 CP.Preclasspool.lookup preclasses nmB = Some cB ->
                                 (forall cB', ~CP.class_loaded classes nmB cB') ->
                                 PA.pc_sub_class classes preclasses (C.preclass_name pc) nmB ->
                                 C.preclass_interface cB = false ->
                                 C.has_premethod (C.preclass_methods pc) md mA ->
                                 C.has_premethod (C.preclass_methods cB) md mB ->
                                 C.premethod_static mA = false ->
                                 C.premethod_static mB = false ->
                                 safe_override (premethod_spec mA) (premethod_spec mB)
 ; preclass_verified_implements :
                               forall iface md ispec,
                                 fst md <> B.init ->
                                 C.preclass_interface pc = false ->
                                 PA.should_implement classes preclasses (C.preclass_name pc) iface ->
                                 PA.interface_reqs_method classes preclasses iface md ispec ->
                                 exists mspec,
                                   PA.minimal_methodspec classes preclasses (C.preclass_name pc) md mspec /\
                                   safe_override mspec ispec
 }.

Lemma correct_specs_preclass_implies_preclass_verified_overrides : forall pc specs,
  CP.Preclasspool.lookup preclasses (C.preclass_name pc) = Some pc ->
  correct_specs_preclass (C.preclass_name pc) specs ->
  preclass_verified_overrides pc.
intros pc specs nm_pc specs_ok. 
destruct specs_ok.
econstructor; intros.
  apply cspecsp_overriding_3 with (md:=md) (nmS:=nmB) (cS:=cB); auto.
  eapply cspecsp_exist0; eauto.

  apply cspecsp_overriding_4 with (md:=md) (nmS:=nmB) (pcS:=cB); auto.
  eapply cspecsp_exist0; eauto.

  destruct (cspecsp_implementing0 pc iface ispec md) as [mspec [mapsto_mspec safe]]; auto.
  exists mspec. split; auto.
  destruct (proj1 (cspecsp_minimal0 md mspec)); eauto.
Save.

Lemma check_preclass'_ok : forall pc nm specs vcs P,
 check_preclass' nm = Val (existT _ vcs (exist _ specs P)) ->
 CP.Preclasspool.lookup preclasses nm = Some pc ->
 C.preclass_name pc = nm ->
 (forall c, ~CP.class_loaded classes nm c) ->
 vcset_ok vcs ->
 preclass_verified_overrides pc.
Proof.
intros pc nm specs vcs specs_ok.
intros check_ok nm_pc pc_nm not_loaded vcs_ok.
subst nm.
clear check_ok.
destruct specs_ok as [[c [loaded _]] |  [pc' [pc_pc0 [X _]]]].
 assumption.
 (* class was loaded *)
 elimtype False. firstorder.
 (* preclass checked out *)
 eauto using correct_specs_preclass_implies_preclass_verified_overrides.
Save.

Lemma check_preclass_ok : forall pc nm specs vcs,
 check_preclass nm = Val (vcs, specs) ->
 CP.Preclasspool.lookup preclasses nm = Some pc ->
 C.preclass_name pc = nm ->
 (forall c, ~CP.class_loaded classes nm c) ->
 vcset_ok vcs ->
 preclass_verified_overrides pc.
Proof.
intros until vcs. intros check_ok nm_pc pc_nm not_loaded vcs_ok.
unfold check_preclass in check_ok.
rewrite nm_pc in check_ok.
destruct (C.preclass_interface pc) as [|] _eqn: iface.
 constructor; intros; congruence.

 destruct (check_preclass' nm) as [r|err] _eqn: check_ok'.
  simpl in *. destruct r as [vcs' [specs' specs_ok]]. injection check_ok as e e'. subst specs' vcs'.
  eapply check_preclass'_ok; eauto.

  discriminate.
Qed.

End WithClasses.

End GenericOverrideChecker.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

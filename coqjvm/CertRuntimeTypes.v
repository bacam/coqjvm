Require Import OrderedTypeEx.
Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import Store.
Require Import Heap.
Require Import Peano_dec.
Require Import Twosig.
Require Import List.
Require Import StoreIface.
Require Import CertRuntimeTypesIface.
Require Import Setoid.

Require Import AnnotationIface.

Module MkCertRuntimeTypes (B  : BASICS)
                          (ANN : ANNOTATION B)
                          (C  : CLASSDATATYPES B ANN)
                          (CP : CLASSPOOL B ANN C)
                          (A  : ASSIGNABILITY B ANN C CP)
                        : CERTRUNTIMETYPES B ANN C CP A.

Inductive rt_val : Set :=
  | rt_int    : B.Int32.t -> rt_val
  | rt_addr   : option Heap.addr_t -> rt_val
  | rt_long   : rt_val
  | rt_double : rt_val
  | rt_float  : rt_val.

Definition val_category : rt_val -> C.value_category :=
  fun v => match v with
  | rt_int _  => C.category1
  | rt_addr _ => C.category1
  | rt_long   => C.category2
  | rt_double => C.category2
  | rt_float  => C.category1
  end.

Record frame : Type := mkFrame
 { frame_op_stack : list rt_val
 ; frame_lvars    : list (option rt_val) (* a local variable entry is None if it is the second part of a cat2 value, or has not been initialised yet *)
 ; frame_pc       : nat
 ; frame_code     : C.code
 ; frame_method   : C.method
 ; frame_class    : C.class
 }.

Definition default_value : C.java_type -> rt_val :=
  fun ty => match ty with
  | C.ty_byte    => rt_int B.Int32.zero
  | C.ty_int     => rt_int B.Int32.zero
  | C.ty_short   => rt_int B.Int32.zero
  | C.ty_char    => rt_int B.Int32.zero
  | C.ty_boolean => rt_int B.Int32.zero
  | C.ty_double  => rt_double
  | C.ty_float   => rt_float
  | C.ty_long    => rt_long
  | C.ty_ref _   => rt_addr None
  end.

Module ClassAndFieldName := PairOrderedType B.Classname B.Fieldname.
Module FullFieldDesc := PairOrderedType ClassAndFieldName C.JavaType_as_UOT.
Module RtVal.
Definition t := rt_val.
End RtVal.
Module FieldStore := Store.MkStore FullFieldDesc RtVal.

Inductive heap_object : Type :=
| hp_object : B.Classname.t -> FieldStore.t -> heap_object.

Module HeapObject.
Definition t:=heap_object.
End HeapObject.
Module PreObjectHeap := MkHeap HeapObject.

(* FIXME: this is wrong: we should have different datatypes for stack and heap
   data *)
Inductive inner_typed_val (classes:CP.cert_classpool) (heap:PreObjectHeap.t)
                  : rt_val -> C.java_type -> Prop :=
| inner_typed_int     : forall i, inner_typed_val classes heap (rt_int i) C.ty_int
| inner_typed_byte    : forall i, inner_typed_val classes heap (rt_int i) C.ty_byte
| inner_typed_short   : forall i, inner_typed_val classes heap (rt_int i) C.ty_short
| inner_typed_char    : forall i, inner_typed_val classes heap (rt_int i) C.ty_char
| inner_typed_boolean : forall i, inner_typed_val classes heap (rt_int i) C.ty_boolean
| inner_typed_float   : inner_typed_val classes heap rt_float C.ty_float
| inner_typed_long    : inner_typed_val classes heap rt_long C.ty_long
| inner_typed_double  : inner_typed_val classes heap rt_double C.ty_double
| inner_typed_null    : forall ty, inner_typed_val classes heap (rt_addr None) (C.ty_ref ty)
| inner_typed_addr    : forall a clsnm fields clsnm',
    PreObjectHeap.lookup heap a = Some (hp_object clsnm fields) ->
    A.assignable classes (C.ty_obj clsnm) (C.ty_obj clsnm') ->
    inner_typed_val classes heap (rt_addr (Some a)) (C.ty_ref (C.ty_obj clsnm')).

Definition well_typed_fieldstore (classes:CP.cert_classpool) (heap:PreObjectHeap.t) (fs:FieldStore.t) :=
  forall clsnm fldnm ty v,
    FieldStore.lookup fs (clsnm, fldnm, ty) = Some v ->
    inner_typed_val classes heap v ty.

Definition well_typed_heap (classes:CP.cert_classpool) (heap:PreObjectHeap.t) :=
  forall a clsnm flds,
    PreObjectHeap.lookup heap a = Some (hp_object clsnm flds) ->
    (exists c, CP.class_loaded classes clsnm c /\ C.class_interface c = false)
     /\
    well_typed_fieldstore classes heap flds.

Lemma preserve_inner_typed : forall classes classes' heap v ty,
  inner_typed_val classes heap v ty ->
  CP.preserve_old_classes classes classes' ->
  inner_typed_val classes' heap v ty.
intros classes classes' heap v ty classes_v_ty preserve.
induction classes_v_ty; try constructor.
 (* remaining case: typed_addr *)
 eapply inner_typed_addr. apply H. eapply A.preserve_assignable; eauto.
Save.

Lemma preserve_well_typed_fieldstore : forall classes classes' heap fs,
  well_typed_fieldstore classes heap fs ->
  CP.preserve_old_classes classes classes' ->
  well_typed_fieldstore classes' heap fs.
unfold well_typed_fieldstore. intros.
eapply preserve_inner_typed; eauto.
Save.

Lemma preserve_well_typed_heap : forall classes classes' heap,
  well_typed_heap classes heap ->
  CP.preserve_old_classes classes classes' ->
  well_typed_heap classes' heap.
unfold well_typed_heap. intros.
destruct (H _ _ _ H1) as [[c c_exists] flds_well_typed].
split. 
 exists c. intuition.
 eapply preserve_well_typed_fieldstore; eassumption.
Save.

Definition cert_heap := fun classes => { h : PreObjectHeap.t | well_typed_heap classes h }.

Program Definition empty_heap : forall classes, cert_heap classes
  := fun classes => PreObjectHeap.empty_heap.
Next Obligation.
unfold well_typed_heap.
intros a clsnm flds lookup.
rewrite PreObjectHeap.lookup_empty in lookup. discriminate.
Save.

Program Definition preserve_cert_heap (classesA classesB:CP.cert_classpool)
                                      (heap:cert_heap classesA)
                                      (poc:CP.preserve_old_classes classesA classesB)
                                    : cert_heap classesB
 := heap.
Next Obligation.
eapply preserve_well_typed_heap.
 destruct heap. apply w.
 apply poc.
Defined.
Implicit Arguments preserve_cert_heap [classesA classesB].

Definition object_field_value (classes:CP.cert_classpool)
                              (heap:cert_heap classes)
                              (addr:addr_t)
                              (fld_cls:B.Classname.t)
                              (fld_nm:B.Fieldname.t)
                              (fld_ty:C.java_type)
                              (v:rt_val)
                            : Prop
 := exists cls_nm, exists flds,
         PreObjectHeap.lookup (proj1_sig heap) addr = Some (hp_object cls_nm flds)
      /\ ((FieldStore.lookup flds (fld_cls,fld_nm,fld_ty) = Some v
           /\ inner_typed_val classes (proj1_sig heap) v fld_ty)
          \/
          (FieldStore.lookup flds (fld_cls,fld_nm,fld_ty) = None
           /\ v = default_value fld_ty)).

Definition object_class (classes:CP.cert_classpool)
                        (heap:cert_heap classes)
                        (addr:addr_t)
                        (cls_nm:B.Classname.t)
                      : Prop
  := exists flds,
          PreObjectHeap.lookup (proj1_sig heap) addr = Some (hp_object cls_nm flds).

Definition object_exists (classes:CP.cert_classpool)
                         (heap:cert_heap classes)
                         (addr:addr_t)
                       : Prop
 := exists cls_nm, exists flds,
          PreObjectHeap.lookup (proj1_sig heap) addr = Some (hp_object cls_nm flds).

Lemma object_field_value_unique : forall classes heap addr fld_cls fld_nm fld_ty v v',
  object_field_value classes heap addr fld_cls fld_nm fld_ty v ->
  object_field_value classes heap addr fld_cls fld_nm fld_ty v' ->
  v = v'.
intros classes heap addr fld_cls fld_nm fld_ty v v' [cls_nm [flds [H1 H2]]] [cls_nm' [flds' [H1' H2']]].
rewrite H1 in H1'. inversion H1'. subst.
destruct H2 as [[H3 H4]|[H3 H4]].
 destruct H2' as [[H3' H4']|[H3' H4']].
  rewrite H3 in H3'. inversion H3'. reflexivity.
  rewrite H3 in H3'. discriminate.
 destruct H2' as [[H3' H4']|[H3' H4']].
  rewrite H3 in H3'. discriminate.
  rewrite H4. rewrite H4'. reflexivity.
Save.

Lemma object_class_unique : forall classes heap addr cls_nm cls_nm',
  object_class classes heap addr cls_nm ->
  object_class classes heap addr cls_nm' ->
  cls_nm = cls_nm'.
intros classes heap addr cls_nm cls_nm' [flds H] [flds' H'].
rewrite H in H'. inversion H'. reflexivity.
Save.
Implicit Arguments object_class_unique [classes heap addr cls_nm cls_nm'].

Lemma field_value_implies_exists : forall classes heap addr fld_cls fld_nm fld_ty v,
  object_field_value classes heap addr fld_cls fld_nm fld_ty v ->
  object_exists classes heap addr.
intros classes heap addr fld_cls fld_nm fld_ty v [cls_nm [flds [H _]]].
exists cls_nm. exists flds. apply H.
Save.

Lemma object_class_implies_class_exists : forall classes heap addr cls_nm,
  object_class classes heap addr cls_nm ->
  exists c, CP.class_loaded classes cls_nm c /\ C.class_interface c = false.
intros classes [heap wth] addr cls_nm [flds H].
destruct (wth _ _ _ H) as [H0 _]. apply H0.
Save.

Lemma object_class_implies_exists : forall classes heap addr cls_nm,
  object_class classes heap addr cls_nm ->
  object_exists classes heap addr.
intros classes heap addr cls_nm [flds H].
exists cls_nm. exists flds. apply H.
Save.

Lemma preserve_object_field_value : forall classesA classesB heap addr fld_cls fld_nm fld_ty v poc,
  object_field_value classesA heap addr fld_cls fld_nm fld_ty v ->
  object_field_value classesB (preserve_cert_heap heap poc) addr fld_cls fld_nm fld_ty v.
intros classesA classesB heap addr fld_cls fld_nm fld_ty v poc [cls_nm [flds [H0 H1]]].
exists cls_nm. exists flds. intuition. left. intuition. 
 eapply preserve_inner_typed; eassumption.
Save.

Lemma preserve_object_class : forall classesA classesB heap addr cls_nm poc,
  object_class classesA heap addr cls_nm ->
  object_class classesB (preserve_cert_heap heap poc) addr cls_nm.
intros classesA classesB heap addr cls_nm poc [flds H].
exists flds. apply H.
Save.

Lemma preserve_object_exists : forall classesA classesB heap addr poc,
  object_exists classesA heap addr ->
  object_exists classesB (preserve_cert_heap heap poc) addr.
intros classesA classesB heap addr pos [cls_nm [flds H]].
exists cls_nm. exists flds. apply H.
Save. 

Lemma not_found_implies_not_exists : forall classes heap addr,
  PreObjectHeap.lookup (proj1_sig heap) addr = None ->
  ~object_exists classes heap addr.
intros classes heap addr not_found.
unfold not. intros [cls_nm [flds found]].
rewrite not_found in found. discriminate.
Save.

Lemma defaults_well_typed : forall classes heap ty, inner_typed_val classes heap (default_value ty) ty.
intros. unfold default_value. destruct ty; constructor.
Save.

Program Definition heap_lookup_field (classes:CP.cert_classpool)
                                     (heap:cert_heap classes)
                                     (addr:addr_t)
                                     (fld_cls:B.Classname.t) (fld_nm:B.Fieldname.t) (fld_ty:C.java_type)
                                   : { v : rt_val | object_field_value classes heap addr fld_cls fld_nm fld_ty v }
                                     + { ~object_exists classes heap addr }
  := match PreObjectHeap.lookup heap addr with
     | Some (hp_object cls_nm flds) =>
        match FieldStore.lookup flds (fld_cls, fld_nm, fld_ty) with
        | Some v =>
           inleft _ v
        | None =>
           inleft _ (default_value fld_ty)
        end
     | None => inright _ _
     end.
Next Obligation.
exists cls_nm. exists flds. intuition. left. intuition.
 destruct heap as [heap wth].
 destruct (wth _ _ _ (sym_eq Heq_anonymous0)) as [_ wtf].
 unfold well_typed_fieldstore in wtf. eapply wtf. symmetry. eassumption.
Defined.
Next Obligation.
exists cls_nm. exists flds. intuition.
Defined.
Next Obligation.
apply not_found_implies_not_exists. symmetry. assumption.
Defined.

Program Definition heap_lookup_class (classes:CP.cert_classpool)
                                     (heap:cert_heap classes)
                                     (addr:addr_t)
                                   : { cls_nm : B.Classname.t | object_class classes heap addr cls_nm }
                                     +{ ~object_exists classes heap addr }
 := match PreObjectHeap.lookup heap addr with
    | Some (hp_object cls_nm flds) => inleft _ cls_nm
    | None => inright _ _
    end.
Next Obligation.
exists flds. symmetry. assumption.
Defined.
Next Obligation.
apply not_found_implies_not_exists. symmetry. assumption.
Save.

(* FIXME: this is wrong: we should have different datatypes for stack and heap
   data *)
Inductive typed_val (classes:CP.cert_classpool) (heap:cert_heap classes)
                  : rt_val -> C.java_type -> Prop :=
| typed_int     : forall i, typed_val classes heap (rt_int i) C.ty_int
| typed_byte    : forall i, typed_val classes heap (rt_int i) C.ty_byte
| typed_short   : forall i, typed_val classes heap (rt_int i) C.ty_short
| typed_char    : forall i, typed_val classes heap (rt_int i) C.ty_char
| typed_boolean : forall i, typed_val classes heap (rt_int i) C.ty_boolean
| typed_float   : typed_val classes heap rt_float C.ty_float
| typed_long    : typed_val classes heap rt_long C.ty_long
| typed_double  : typed_val classes heap rt_double C.ty_double
| typed_null    : forall ty, typed_val classes heap (rt_addr None) (C.ty_ref ty)
| typed_addr    : forall a clsnm clsnm',
    object_class classes heap a clsnm ->
    A.assignable classes (C.ty_obj clsnm) (C.ty_obj clsnm') ->
    typed_val classes heap (rt_addr (Some a)) (C.ty_ref (C.ty_obj clsnm')).

Lemma typed_val_implies_inner_typed_val : forall classes heap v ty,
  typed_val classes heap v ty ->
  inner_typed_val classes (proj1_sig heap) v ty.
intros classes heap v ty v_ty.
destruct v_ty; try constructor.
 destruct H as [flds H].
 eapply inner_typed_addr; eassumption.
Save.

Definition inner_preserve_classes :=
  fun heap heap' =>
  forall addr cls_nm flds, PreObjectHeap.lookup heap addr = Some (hp_object cls_nm flds) ->
                           exists flds', PreObjectHeap.lookup heap' addr = Some (hp_object cls_nm flds').

Definition heap_preserve_classes :=
  fun classes (heap heap':cert_heap classes) =>
  forall addr cls_nm, object_class classes heap addr cls_nm ->
                      object_class classes heap' addr cls_nm.

Definition heap_preserve_most_fields :=
  fun classes (heap heap':cert_heap classes) addr fld_cls fld_nm fld_ty =>
  forall addr' fld_cls' fld_nm' fld_ty' v,
    object_field_value classes heap addr' fld_cls' fld_nm' fld_ty' v ->
    (addr <> addr' \/ (fld_cls,fld_nm,fld_ty) <> (fld_cls',fld_nm',fld_ty')) ->
    object_field_value classes heap' addr' fld_cls' fld_nm' fld_ty' v.

Lemma inner_preserve_classes_implies_preserve_classes : forall classes heap heap',
  inner_preserve_classes (proj1_sig heap) (proj1_sig heap') ->
  heap_preserve_classes classes heap heap'.
intros classes [heap wth] [heap' wth'] p_h_h'.
simpl in *. 
unfold inner_preserve_classes in p_h_h'.
unfold heap_preserve_classes. intros addr cls_nm [flds lookup_ok].
unfold object_class. eapply p_h_h'. apply lookup_ok.
Save.

Lemma inner_preserve_inner_typed_val : forall classes heap heap' v ty,
  inner_preserve_classes heap heap' ->
  inner_typed_val classes heap v ty ->
  inner_typed_val classes heap' v ty.
intros classes heap heap' v ty pc v_ty.
destruct v_ty; try constructor.
 destruct (pc a clsnm fields H).
 eapply inner_typed_addr; eassumption.
Save.

Lemma inner_preserve_well_typed_fieldstore : forall classes heap heap' fields,
  inner_preserve_classes heap heap' ->
  well_typed_fieldstore classes heap fields ->
  well_typed_fieldstore classes heap' fields.
intros clases heap heap' fields p_heap_heap' wtf.
unfold well_typed_fieldstore in *.
intros clsnm fldnm ty v lookup_ok.
eapply inner_preserve_inner_typed_val; eauto.
Save.

Lemma update_preserves : forall heap heap' addr cls_nm fields fields',
  PreObjectHeap.lookup heap addr = Some (hp_object cls_nm fields) ->
  PreObjectHeap.update heap addr (hp_object cls_nm fields') = Some heap' ->
  inner_preserve_classes heap heap'.
intros heap heap' addr cls_nm fields fields' lookup_ok update_ok.
unfold inner_preserve_classes. intros addr' cls_nm' flds' lookup'_ok.
destruct (positive_eq_dec addr' addr) as [addr'_eq_addr | addr'_neq_addr].
 subst. exists fields'. rewrite lookup'_ok in lookup_ok. inversion lookup_ok. subst. eapply PreObjectHeap.lookup_update. apply update_ok.
 exists flds'. eapply PreObjectHeap.indep_lookup; eassumption.
Save.

Lemma new_preserves : forall heap heap' addr cls_nm,
  PreObjectHeap.new heap cls_nm = (heap', addr) ->
  inner_preserve_classes heap heap'.
intros heap heap' addr cls_nm new_eq.
unfold inner_preserve_classes. intros addr' cls_nm' flds' lookup.
exists flds'. eapply PreObjectHeap.new_preserves.
 apply new_eq.
 apply lookup.
Save.

Lemma neq_symm : forall (A:Type) (a b:A), a<>b -> b<>a.
unfold not. intros. apply H. symmetry. assumption.
Save.
Implicit Arguments neq_symm [A a b].

Add Relation FullFieldDesc.t FullFieldDesc.eq
 reflexivity proved by FullFieldDesc.eq_refl
 symmetry proved by FullFieldDesc.eq_sym
 transitivity proved by FullFieldDesc.eq_trans
 as fullfielddesc_setoid.

Add Morphism FieldStore.lookup
 with signature (eq (A:=FieldStore.t)) ==> FullFieldDesc.eq ==> (eq (A:=option rt_val))
 as fieldstore_lookup_mor.
apply FieldStore.lookup_eq.
Save.

Lemma FullFieldDesc_not_eq_neq : forall (x y:FullFieldDesc.t), ~FullFieldDesc.eq x y -> x<>y.
intros. unfold not. intros. subst. apply H. apply FullFieldDesc.eq_refl.
Save.

Lemma FullFieldDesc_eq : forall (x y:FullFieldDesc.t), FullFieldDesc.eq x y -> x = y.
destruct x as [[x1 x2] x3]. destruct y as [[y1 y2] y3].
unfold FullFieldDesc.eq.
unfold ClassAndFieldName.eq.
simpl. intuition congruence.
Save.

Hint Resolve FullFieldDesc_not_eq_neq FullFieldDesc.lt_not_eq FullFieldDesc_eq.
Hint Immediate FullFieldDesc.eq_sym.

Lemma FullFieldDesc_eq_dec : forall (x y:FullFieldDesc.t), {x=y}+{x<>y}.
intros x y. destruct (FullFieldDesc.compare x y); auto.
 right. unfold not. intro. refine (FullFieldDesc.lt_not_eq l _). apply FullFieldDesc.eq_sym. subst. reflexivity.
Defined.

Program Definition heap_update_field (classes:CP.cert_classpool)
                                     (heap:cert_heap classes)
                                     (addr:addr_t)
                                     (fld_cls:B.Classname.t)
                                     (fld_nm:B.Fieldname.t)
                                     (fld_ty:C.java_type)
                                     (v:rt_val) 
                                     (p:typed_val classes heap v fld_ty)
 : { heap' : cert_heap classes | object_field_value classes heap' addr fld_cls fld_nm fld_ty v
                                 /\ heap_preserve_classes classes heap heap'
                                 /\ heap_preserve_most_fields classes heap heap' addr fld_cls fld_nm fld_ty }
   + { ~object_exists classes heap addr }
 := match PreObjectHeap.lookup heap addr with
    | Some (hp_object cls_nm fields) =>
       let fields' := FieldStore.update fields (fld_cls,fld_nm,fld_ty) v in
        match PreObjectHeap.update heap addr (hp_object cls_nm fields') with
        | None => _
        | Some heap' => inleft _ heap'
        end
    | None => inright _ _
    end.
Next Obligation.
elimtype False.
destruct (PreObjectHeap.update_ok _ _ _ (hp_object cls_nm (FieldStore.update fields (fld_cls,fld_nm,fld_ty) v)) (sym_eq Heq_anonymous0)) as [heap' heap'_eq].
assert (None = Some heap'). rewrite Heq_anonymous. rewrite <- heap'_eq. reflexivity. discriminate.
Defined.
Next Obligation.
destruct heap as [heap wth]. simpl in *.
assert (preserve:inner_preserve_classes heap heap').
 eapply update_preserves; eauto.
unfold well_typed_heap. intros a clsnm flds lookup.
destruct (positive_eq_dec a addr) as [a_eq_addr|a_neq_addr].
 (* addr = a *)
 subst. rewrite (PreObjectHeap.lookup_update _ _ _ _ (sym_eq Heq_anonymous)) in lookup.
 inversion lookup. subst. clear lookup. destruct (wth _ _ _ (sym_eq Heq_anonymous0)). split.
  assumption.
  unfold well_typed_fieldstore. intros fld_cls2 fld_nm2 fld_ty2 v2 v2_lookup.
  destruct (FullFieldDesc_eq_dec (fld_cls,fld_nm,fld_ty) (fld_cls2,fld_nm2,fld_ty2)) as [fld_eq_fld2|fld_neq_fld2].
   inversion fld_eq_fld2. simpl in H4. subst.
   rewrite FieldStore.lookup_update in v2_lookup. inversion v2_lookup. subst.
    eapply inner_preserve_inner_typed_val; eauto. 
     change heap with (proj1_sig (exist _ heap wth)). apply (typed_val_implies_inner_typed_val classes). apply p.
   rewrite FieldStore.indep_lookup in v2_lookup; [|auto].
    eapply inner_preserve_inner_typed_val; eauto.
 (* a <> addr *)
 destruct (wth _ _ _ (PreObjectHeap.indep_lookup_2 (sym_eq Heq_anonymous) lookup a_neq_addr)). split.
  assumption.
  eapply inner_preserve_well_typed_fieldstore; eauto.
Defined.
Next Obligation.
destruct heap as [heap wth].
assert (preserve:inner_preserve_classes heap heap').
 eapply update_preserves; eauto.
split.
 (* object_field_value *)
 unfold object_field_value. simpl.
 exists cls_nm. exists (FieldStore.update fields (fld_cls, fld_nm, fld_ty) v). split.
  eapply PreObjectHeap.lookup_update. symmetry. apply Heq_anonymous.
  left. split.
   apply FieldStore.lookup_update.
   eapply inner_preserve_inner_typed_val; eauto.
    change heap with (proj1_sig (exist _ heap wth)). apply (typed_val_implies_inner_typed_val classes). apply p.
 (* others *)
 split.
  (* heap_preserve_classes *)
  apply inner_preserve_classes_implies_preserve_classes. simpl. apply preserve.
  (* heap_preserve_most_fields *)
  unfold heap_preserve_most_fields. unfold object_field_value. simpl in *.
  intros addr' fld_cls' fld_nm' fld_ty' v0 [cls_nm' [flds [H1 H2]]] [addr_neq_addr'|fld_neq_fld'].
   (* addr <> addr' *)
   exists cls_nm'. exists flds. split.
    eapply PreObjectHeap.indep_lookup.
     symmetry. apply Heq_anonymous.
     apply H1.
     apply neq_symm. apply addr_neq_addr'.
    destruct H2 as [[H2 H3]|[H2 H3]].
     left. split.
      assumption.
      eapply inner_preserve_inner_typed_val; eauto.
     right. auto.
   (* fld <> fld' *)
   destruct (positive_eq_dec addr addr') as [addr_eq_addr' | addr_neq_addr'].
    (* addr = addr' *)
    subst. exists cls_nm. exists (FieldStore.update fields (fld_cls, fld_nm, fld_ty) v). split.
     eapply PreObjectHeap.lookup_update. symmetry. apply Heq_anonymous.
     rewrite <- Heq_anonymous0 in H1. inversion H1. subst. 
     destruct H2 as [[H2 H3]|[H2 H3]].
      left. split.
       rewrite FieldStore.indep_lookup; auto.
       eapply inner_preserve_inner_typed_val; eauto.
      right. rewrite FieldStore.indep_lookup; auto.
    (* addr <> addr' *)
    exists cls_nm'. exists flds. split.
     eapply PreObjectHeap.indep_lookup.
      symmetry. apply Heq_anonymous.
      apply H1.
      apply neq_symm. apply addr_neq_addr'.
     destruct H2 as [[H2 H3]|[H2 H3]].
      left. split.
       assumption.
       eapply inner_preserve_inner_typed_val; eauto.
      right. auto.
Defined.
Next Obligation.
apply not_found_implies_not_exists. symmetry. apply Heq_anonymous.
Defined.

Definition heap_preserve_fields :=
  fun classes (heap heap':cert_heap classes) =>
  forall addr fld_cls fld_nm fld_ty v,
    object_field_value classes heap addr fld_cls fld_nm fld_ty v ->
    object_field_value classes heap' addr fld_cls fld_nm fld_ty v.

Definition heap_preserve_existence :=
  fun classes (heap heap':cert_heap classes) =>
  forall addr,
    object_exists classes heap addr ->
    object_exists classes heap' addr.

Program Definition heap_new (classes:CP.cert_classpool)
                            (heap:cert_heap classes)
                            (cls_nm:B.Classname.t)
                            (p:exists c, CP.class_loaded classes cls_nm c /\ C.class_interface c = false)
                          : { heap' : cert_heap classes, addr : addr_t |
                                    object_class classes heap' addr cls_nm
                                 /\ ~object_exists classes heap addr
                                 /\ heap_preserve_existence classes heap heap'
                                 /\ heap_preserve_classes classes heap heap'
                                 /\ heap_preserve_fields classes heap heap' }
 := let x := PreObjectHeap.new heap (hp_object cls_nm FieldStore.empty) in
     pack2 _ (fst x) (snd x) _.
Next Obligation.
destruct (PreObjectHeap.new_elim (proj1_sig heap) (hp_object cls_nm FieldStore.empty)) as [heap' [addr new_eq]].
rewrite new_eq.
destruct heap as [heap wth]. simpl in *.
assert (preserve:inner_preserve_classes heap heap').
 eapply new_preserves; eauto.
unfold well_typed_heap.
intros a clsnm flds lookup.
destruct (positive_eq_dec a addr) as [a_eq_addr | a_neq_addr].
 (* a = addr *)
 subst. rewrite (PreObjectHeap.new_lookup _ _ _ _ new_eq) in lookup. inversion lookup. subst. split.
  exists p. auto.
  unfold well_typed_fieldstore. intros. rewrite FieldStore.lookup_empty in H1. discriminate.
 (* a <> addr *)
 destruct (wth a clsnm flds) as [H1 H2].
  eapply PreObjectHeap.new_preserves_2.
   apply new_eq.
   apply lookup.
   apply neq_symm. apply a_neq_addr.
  split.
   apply H1.
   eapply inner_preserve_well_typed_fieldstore; eauto.
Defined.
Next Obligation.
destruct (PreObjectHeap.new_elim (proj1_sig heap) (hp_object cls_nm FieldStore.empty)) as [heap' [addr new_eq]].
split.
 (* object_class *)
 unfold object_class. simpl. rewrite new_eq. simpl.
 exists FieldStore.empty. eapply PreObjectHeap.new_lookup. apply new_eq.
 split.
  (* ~object_exists *) 
  rewrite new_eq. simpl.  
  apply not_found_implies_not_exists. eapply PreObjectHeap.new_was_None. apply new_eq.
  split.
   (* heap_preserve_existence *)
   unfold heap_preserve_existence. unfold object_exists.
   simpl. rewrite new_eq. simpl.
   intros addr' [cls_nm' [flds' lookup]].
   exists cls_nm'. exists flds'. eapply PreObjectHeap.new_preserves; eassumption.
   split.
    (* heap_preserve_classes *)
    unfold heap_preserve_classes. unfold object_class.
    simpl. rewrite new_eq. simpl.
    intros addr' cls_nm' [flds' lookup]. 
    exists flds'. eapply PreObjectHeap.new_preserves; eassumption.
    (* heap_preserve_fields *)
    unfold heap_preserve_fields. unfold object_field_value.
    simpl. rewrite new_eq. simpl.
    intros addr' fld_cls fld_nm fld_ty v [cls_nm' [flds' [lookup H]]].
    exists cls_nm'. exists flds'. split.
     eapply PreObjectHeap.new_preserves; eassumption.
     destruct H as [[H H0]|H].
      left. split.
       assumption.
       eapply inner_preserve_inner_typed_val.
        eapply new_preserves. apply new_eq.
        apply H0.
      right. apply H.
Defined.

Definition type_check_rt_val : forall classes heap ty v,
  {typed_val classes heap ty v}+{~typed_val classes heap ty v}.
intros classes heap ty v.
destruct v; destruct ty;
  try (left; constructor); try (right; unfold not; intro H; inversion H; fail).
 destruct j.
 (* addr ref *)
 destruct o.
  (* addr is Some *)
  destruct (heap_lookup_class classes heap a) as [[cls_nm H]|no_object].
   (* object exists *)
   destruct (A.is_assignable classes (C.ty_obj cls_nm) (C.ty_obj t)) as [is_assignable|not_assignable].
    (* is_assignable *)
    left. eapply typed_addr; eassumption.
    (* not assignable *)
    right. unfold not. intro H0. inversion H0.
    subst. rewrite (object_class_unique H H3) in not_assignable. apply (not_assignable H4).
   (* object doesn't exist *)
   right. unfold not. intro H0. inversion H0.
   apply no_object. eapply object_class_implies_exists. apply H2.
  (* addr is None *) 
  left. apply typed_null. 
 (* addr arr *)
 destruct o.
  right. unfold not. intro H. inversion H.
  left. apply typed_null.
Defined.


(* Certified static fields stores *)

Definition well_typed_statics_fieldstore (classes:CP.cert_classpool) (heap:PreObjectHeap.t) (fs:FieldStore.t) :=
  forall fld_cls fld_nm fld_ty v,
    FieldStore.lookup fs (fld_cls, fld_nm, fld_ty) = Some v ->
    (exists c, exists f, CP.class_loaded classes fld_cls  c
                         /\ C.FieldList.lookup (C.class_fields c) (fld_nm, fld_ty) = Some f
                         /\ C.field_static f = true)
    /\
    inner_typed_val classes heap v fld_ty.

Definition cert_fieldstore :=
  fun classes (heap:cert_heap classes) => { f : FieldStore.t | well_typed_statics_fieldstore classes (proj1_sig heap) f }.

Program Definition empty_fieldstore (classes:CP.cert_classpool)
                                    (heap:cert_heap classes)
                                  : cert_fieldstore classes heap
  := FieldStore.empty.
Next Obligation.
unfold well_typed_statics_fieldstore.
intros clsnm fldnm ty v lookup.
rewrite FieldStore.lookup_empty in lookup.
discriminate.
Save.

Definition fieldstore_value (classes:CP.cert_classpool)
                            (heap:cert_heap classes)
                            (fields:cert_fieldstore classes heap)
                            (fld_cls:B.Classname.t)
                            (fld_nm:B.Fieldname.t)
                            (fld_ty:C.java_type)
                            (v:rt_val)
                          : Prop
  := (FieldStore.lookup (proj1_sig fields) (fld_cls, fld_nm, fld_ty) = Some v
      /\ inner_typed_val classes (proj1_sig heap) v fld_ty)
     \/
     (FieldStore.lookup (proj1_sig fields) (fld_cls, fld_nm, fld_ty) = None
      /\ v = default_value fld_ty
      /\ (exists c, exists f, CP.class_loaded classes fld_cls c
                              /\ C.FieldList.lookup (C.class_fields c) (fld_nm, fld_ty) = Some f
                              /\ C.field_static f = true)).

Program Definition preserve_cert_fieldstore_over_classes
   (classesA:CP.cert_classpool)
   (classesB:CP.cert_classpool)
   (heap:cert_heap classesA)
   (fields:cert_fieldstore classesA heap)
   (poc:CP.preserve_old_classes classesA classesB)
 : cert_fieldstore classesB (preserve_cert_heap heap poc)
:= fields.
Next Obligation.
unfold well_typed_statics_fieldstore.
intros clsnm fldnm ty v lookup.
destruct fields as [fields wtf].
simpl in *.
destruct (wtf _ _ _ _ lookup) as [[c [f [c_exists [f_exists f_static]]]] v_typed].
split.
 exists c. exists f. intuition.
 eapply preserve_inner_typed; eassumption.
Defined.
Implicit Arguments preserve_cert_fieldstore_over_classes [classesA classesB heap].

Lemma preserve_fieldstore_value_over_classes :
  forall classesA classesB heap fields fld_cls fld_nm fld_ty v
    (poc:CP.preserve_old_classes classesA classesB),
    fieldstore_value classesA heap fields fld_cls fld_nm fld_ty v ->
    fieldstore_value classesB (preserve_cert_heap heap poc) (preserve_cert_fieldstore_over_classes fields poc) fld_cls fld_nm fld_ty v.
intros classesA classesB heap fields fld_cls fld_nm fld_ty v pos value_v.
destruct fields as [fields wtf].
unfold fieldstore_value in *. simpl in *.
destruct value_v as [[lookup_v typed_v] | [lookup_None [v_Default [c [f [c_exists [f_exists f_static]]]]]]].
 left. split.
  apply lookup_v.
  eapply preserve_inner_typed; eassumption.
 right. intuition. exists c. exists f. intuition.
Save.

Lemma heap_preserve_classes_implies_inner : forall classes heapA heapB,
  heap_preserve_classes classes heapA heapB ->
  inner_preserve_classes (proj1_sig heapA) (proj1_sig heapB).
intros classes heapA heapB hpc.
unfold inner_preserve_classes.
intros addr cls_nm flds lookup.
unfold heap_preserve_classes in hpc.
destruct (hpc addr cls_nm) as [flds' lookup'].
 exists flds. apply lookup.
 exists flds'. apply lookup'.
Save.

Program Definition preserve_cert_fieldstore_over_heap
   (classes:CP.cert_classpool)
   (heapA:cert_heap classes)
   (heapB:cert_heap classes)
   (fields:cert_fieldstore classes heapA)
   (hpc:heap_preserve_classes classes heapA heapB)
 : cert_fieldstore classes heapB
:= fields.
Next Obligation.
unfold well_typed_statics_fieldstore.
intros clsnm fldnm ty v lookup.
destruct fields as [fields wtf].
simpl in *.
destruct (wtf _ _ _ _ lookup) as [[c [f [c_exists [f_exists f_static]]]] typed_v].
split.
 exists c. exists f. intuition.
 eapply inner_preserve_inner_typed_val.
  apply heap_preserve_classes_implies_inner. apply hpc.
  apply typed_v.
Defined.
Implicit Arguments preserve_cert_fieldstore_over_heap [classes heapA heapB].

Lemma preserve_fieldstore_value_over_heap :
  forall classes heapA heapB fields fld_cls fld_nm fld_ty v
    (hpc:heap_preserve_classes classes heapA heapB),
    fieldstore_value classes heapA fields fld_cls fld_nm fld_ty v ->
    fieldstore_value classes heapB (preserve_cert_fieldstore_over_heap fields hpc) fld_cls fld_nm fld_ty v.
intros classes heapA heapB fields fld_cls fld_nm fld_ty v hpc value_v.
unfold fieldstore_value in *.
destruct fields as [fields wtf]. simpl in *.
destruct value_v as [[lookup_v typed_v] | [lookup_None [v_default [c [f [c_exists [f_exists f_static]]]]]]].
 left. split.
  apply lookup_v.
  eapply inner_preserve_inner_typed_val.
   apply heap_preserve_classes_implies_inner. apply hpc.
   apply typed_v.
 right. intuition. exists c. exists f. intuition.
Save. 

Program Definition fieldstore_lookup
   (classes:CP.cert_classpool)
   (heap:cert_heap classes)
   (fields:cert_fieldstore classes heap)
   (fld_cls:B.Classname.t)
   (fld_nm:B.Fieldname.t)
   (fld_ty:C.java_type)
   (f_exists:exists c, exists f, CP.class_loaded classes fld_cls c
                                 /\ C.FieldList.lookup (C.class_fields c) (fld_nm,fld_ty) = Some f
                                 /\ C.field_static f = true)
 : { v : rt_val | fieldstore_value classes heap fields fld_cls fld_nm fld_ty v }
:= match FieldStore.lookup fields (fld_cls,fld_nm,fld_ty) with
   | None => default_value fld_ty
   | Some v => v
   end.
Next Obligation.
right. split.
 symmetry. apply Heq_anonymous.
 intuition. exists f_exists. exists H. intuition.
Defined.
Next Obligation.
destruct fields as [fields wtf].
destruct (wtf _ _ _ _ (sym_eq Heq_anonymous)) as [_ typed_v].
left. split.
 symmetry. assumption.
 apply typed_v.
Defined.

Definition fieldstore_preserve_most_fields :=
  fun classes heap fields fields' fld_cls fld_nm fld_ty =>
  forall fld_cls' fld_nm' fld_ty' v,
    fieldstore_value classes heap fields fld_cls' fld_nm' fld_ty' v ->
    (fld_cls,fld_nm,fld_ty) <> (fld_cls',fld_nm',fld_ty') ->
    fieldstore_value classes heap fields' fld_cls' fld_nm' fld_ty' v.

Program Definition fieldstore_update
   (classes:CP.cert_classpool)
   (heap:cert_heap classes)
   (fields:cert_fieldstore classes heap)
   (fld_cls:B.Classname.t)
   (fld_nm:B.Fieldname.t)
   (fld_ty:C.java_type)
   (v:rt_val)
   (well_typed:typed_val classes heap v fld_ty)
   (f_exists:exists c, exists f, CP.class_loaded classes fld_cls c
                                 /\ C.FieldList.lookup (C.class_fields c) (fld_nm,fld_ty) = Some f
                                 /\ C.field_static f = true)
 : { fields' : cert_fieldstore classes heap |
       fieldstore_value classes heap fields' fld_cls fld_nm fld_ty v
    /\ fieldstore_preserve_most_fields classes heap fields fields' fld_cls fld_nm fld_ty }
:= FieldStore.update fields (fld_cls, fld_nm, fld_ty) v.
Next Obligation.
destruct fields as [fields wtf].
simpl. unfold well_typed_statics_fieldstore.
intros fld_cls' fld_nm' fld_ty' v' lookup.
destruct (FullFieldDesc_eq_dec (fld_cls, fld_nm, fld_ty) (fld_cls',fld_nm',fld_ty')) as [f_eq_f' | f_neq_f'].
 (* fields equal *)
 inversion f_eq_f'. subst.
 rewrite FieldStore.lookup_update in lookup.
 inversion lookup. subst. split. 
  exists f_exists. exists H. intuition.
  apply typed_val_implies_inner_typed_val. apply well_typed.
 (* fields not equal *)
 rewrite FieldStore.indep_lookup in lookup; [|auto].
 apply (wtf _ _ _ _ lookup).
Save.
Next Obligation.
destruct fields as [fields wtf].
split.
 (* fieldstore_value *)
 unfold fieldstore_value.
 simpl. left. split.
  apply FieldStore.lookup_update.
  apply typed_val_implies_inner_typed_val. apply well_typed.
 (* fieldstore_preserve_most_fields *)
 unfold fieldstore_preserve_most_fields. unfold fieldstore_value. simpl.
 intros fld_cls' fld_nm' fld_ty' v' v'_lookup not_eq.
 destruct v'_lookup as [[v'_lookup v'_typed] | [v'_lookup v'_default]].
  (* field was originally there *)
  left. split.
   rewrite FieldStore.indep_lookup; auto.
   assumption.
  right. split.
   rewrite FieldStore.indep_lookup; auto.
   assumption.
Save.

Record pre_state (A:Type) : Type := mkState
 { state_frame_stack   : list frame
 ; state_classes       : CP.cert_classpool
 ; state_object_heap   : cert_heap state_classes
 ; state_static_fields : cert_fieldstore state_classes state_object_heap
 ; state_res           : A
 ; state_reslimit      : A
 }.
Implicit Arguments mkState [A].



End MkCertRuntimeTypes.

 


















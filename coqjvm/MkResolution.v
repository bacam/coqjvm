Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import AssignabilityIface.
Require Import ResolutionIface.
Require Import List.
Require Import ListExt.
Require Import Twosig.
Require Import OptionExt.
Require        BoolExt.

Require Import AnnotationIface.

(* TODO: remove *)
Set Asymmetric Patterns.

Module MkResolution (B : BASICS)
                    (ANN : ANNOTATION B)
                    (C : CLASSDATATYPES B ANN)
                    (CP : CLASSPOOL B ANN C)
                    (A  : ASSIGNABILITY B ANN C CP)
                  : RESOLUTION B ANN C CP A.

Import CP.

Definition check_class_access : B.Classname.t -> C.class -> option CP.exn :=
  fun caller target => None. (*if C.class_public target then None else Some errIllegalAccess.*)
(* FIXME: should also check that they are in the same package *)

Definition resolve_class : forall (caller target:B.Classname.t) classes preclasses,
  {LOAD classes, preclasses ~~> classes' & c : C.class | class_loaded classes' target c }
  :=
  fun caller target classes preclasses =>
  let P := fun classes' c => CP.class_loaded classes' target c in
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

Definition check_method_access : B.Classname.t -> C.class -> C.method -> option CP.exn :=
  fun caller cls meth =>
  None. (* FIXME: do the proper access control checks here *)

Lemma d_inter_here_helper : forall classes nmA nmB interfaces i2,
  nmA = nmB ->
  i2 = nmB::interfaces ->
  A.direct_super_interface classes i2 nmA.
intros. subst. apply A.d_inter_here.
Save.
Implicit Arguments d_inter_here_helper [nmA nmB interfaces i2].

Lemma dsi_fix : forall classes i1 i2 nm,
  i2 = i1 ->
  A.direct_super_interface classes i1 nm ->
  A.direct_super_interface classes i2 nm.
intros. subst. assumption.
Save.
Implicit Arguments dsi_fix [classes i1 i2 nm].

Fixpoint method_lookup_interfaces (classes:CP.cert_classpool)
                                  (interfaces:list B.Classname.t)
                                  (m:B.Methodname.t)
                                  (d:C.descriptor)
                                  (gil:CP.good_interface_list2 classes interfaces)
                                  {struct gil}
                                : option { c : C.class, meth : C.method |
                                           CP.class_loaded classes (C.class_name c) c /\
                                           C.MethodList.lookup (C.class_methods c) (m,d) = Some meth /\
                                           C.class_interface c = true /\
                                           A.direct_super_interface classes interfaces (C.class_name c) }
  :=
  let P := fun c meth => CP.class_loaded classes (C.class_name c) c /\
                         C.MethodList.lookup (C.class_methods c) (m,d) = Some meth /\
                         C.class_interface c = true /\
                         A.direct_super_interface classes interfaces (C.class_name c)
  in
  match list_informative interfaces with
  | inleft (existS nmI (exist rest e)) =>
     let not_not_there := CP.good_interface_list2_not_not_there gil e in
      match CP.class_loaded_dec classes nmI with
      | inleft (exist cI I_exists) =>
         let is_interface := CP.gil2_gives_interface gil e I_exists in
         match C.MethodList.lookup_informative (C.class_methods cI) (m,d) with
         | inleft (exist meth meth_exists) =>
            let dsi_evidence := d_inter_here_helper classes (CP.cert_classpool_names_2 I_exists) e in
            let I_exists := CP.cert_classpool_names I_exists in
            Some (pack2 P cI meth (conj I_exists (conj meth_exists (conj is_interface dsi_evidence))))
         | inright _ =>
            let gil_super := CP.good_interface_list2_inv_1 gil e I_exists in
            match method_lookup_interfaces classes (C.class_interfaces cI) m d gil_super with
            | Some (pack2 cI meth (conj I_exists2 (conj meth_exists (conj is_interface2 dsi_evidence)))) =>
               let new_dsi_evidence := dsi_fix e (A.d_inter_step_up _ _ _ _ _ I_exists is_interface dsi_evidence) in
               Some (pack2 P cI meth (conj I_exists2 (conj meth_exists (conj is_interface2 new_dsi_evidence))))
            | None =>
               let gil_rest := CP.good_interface_list2_inv_2 gil e in
               match method_lookup_interfaces classes rest m d gil_rest with
               | Some (pack2 cI meth (conj I_exists2 (conj meth_exists (conj is_interface dsi_evidence)))) =>
                  let new_dsi_evidence := dsi_fix e (A.d_inter_step_along _ _ _ nmI dsi_evidence) in
                  Some (pack2 P cI meth (conj I_exists2 (conj meth_exists (conj is_interface new_dsi_evidence))))
               | None =>
                  None
               end
            end
          end
      | inright not_there =>
         match not_not_there not_there with end
      end
  | inright _ =>
     None
  end.

Fixpoint method_lookup_all_interfaces (classes:CP.cert_classpool)
                                      (nm:option B.Classname.t)
                                      (m:B.Methodname.t)
                                      (d:C.descriptor)
                                      (scc:CP.super_class_chain classes nm)
                                      {struct scc}
                                    : option { c : C.class, meth : C.method |
                                               CP.class_loaded classes (C.class_name c) c /\
                                               C.MethodList.lookup (C.class_methods c) (m,d) = Some meth /\
                                               C.class_interface c = true /\
                                               (exists s_nm, nm = Some s_nm /\ A.class_implements classes s_nm (C.class_name c)) }
 :=
 let P2 := fun c s_nm => nm = Some s_nm /\ A.class_implements classes s_nm (C.class_name c) in
 let P := fun c meth => CP.class_loaded classes (C.class_name c) c /\
                        C.MethodList.lookup (C.class_methods c) (m,d) = Some meth /\
                        C.class_interface c = true /\
                        ex (P2 c)
 in
 match option_informative nm with
 | inleft (exist s_nm s_nm_eq) =>
    let not_not_there := CP.super_class_chain_not_not_there s_nm_eq scc in
    match CP.class_loaded_dec classes s_nm with
    | inleft (exist sc sc_exists) =>
       let gil := CP.cert_classpool_gives_gil2 sc_exists in
       match method_lookup_interfaces classes (C.class_interfaces sc) m d gil with
       | Some (pack2 cI meth (conj I_exists (conj meth_exists (conj is_interface dsi_evidence)))) =>
          let is_class := CP.scc_gives_class s_nm_eq scc sc_exists in
          let implements_proof := ex_intro (P2 cI) s_nm (conj s_nm_eq (A.cl_impls_direct sc_exists is_class dsi_evidence)) in
          Some (pack2 P cI meth (conj I_exists (conj meth_exists (conj is_interface implements_proof))))
       | None =>
          let scc := CP.super_class_chain_inv sc_exists s_nm_eq scc in
          match method_lookup_all_interfaces classes (C.class_super_class sc) m d scc with
          | Some (pack2 cI meth (conj I_exists (conj meth_exists (conj is_interface implements_proof)))) =>
             let implements_proof2 :=
               match implements_proof with
               | ex_intro s_nm' (conj s_nm'_eq implements_proof) =>
                  ex_intro (P2 cI) s_nm (conj s_nm_eq (A.cl_impls_super sc_exists s_nm'_eq implements_proof))
               end
             in
             Some (pack2 P cI meth (conj I_exists (conj meth_exists (conj is_interface implements_proof2))))
          | None =>
             None
          end
       end
    | inright not_there =>
       match not_not_there not_there with end
    end
 | inright _ =>
   None
 end.


Lemma fixed_sub_class_refl : forall classes nm c,
  CP.class_loaded classes nm c -> A.sub_class classes nm (C.class_name c).
intros. rewrite (CP.cert_classpool_names_2 H). eapply A.sub_class_refl. eauto.
Defined.
Implicit Arguments fixed_sub_class_refl [classes nm c].

Lemma fixed_sub_class_step : forall classes nm c x,
  CP.class_loaded classes nm c ->
  (exists s_nm, C.class_super_class c = Some s_nm /\ A.sub_class classes s_nm x) ->
  A.sub_class classes nm x.
intros. destruct H0. destruct H0.
eapply A.sub_class_step; eauto.
Save.
Implicit Arguments fixed_sub_class_step [classes nm c x].

Fixpoint method_lookup_super_classes (classes:CP.cert_classpool)
                                     (nm:option B.Classname.t)
                                     (m:B.Methodname.t)
                                     (d:C.descriptor)
                                     (scc:CP.super_class_chain classes nm)
                                     {struct scc}
                                   : option { c : C.class, meth : C.method |
                                              CP.class_loaded classes (C.class_name c) c /\
                                              C.MethodList.lookup (C.class_methods c) (m,d) = Some meth /\
                                              C.class_interface c = false /\
                                              (exists s_nm, nm = Some s_nm /\ A.sub_class classes s_nm (C.class_name c)) }
 :=
 let P2 := fun c s_nm => nm = Some s_nm /\ A.sub_class classes s_nm (C.class_name c) in
 let P := fun c meth => CP.class_loaded classes (C.class_name c) c /\
                        C.MethodList.lookup (C.class_methods c) (m,d) = Some meth /\
                        C.class_interface c = false /\
                        ex (P2 c)
 in
 match option_informative nm with
 | inleft (exist s_nm s_nm_eq) =>
    match CP.class_loaded_dec classes s_nm with
    | inleft (exist sc sc_exists) =>
       match C.MethodList.lookup_informative (C.class_methods sc) (m,d) with
       | inleft (exist meth meth_exists) =>
          let is_class := CP.scc_gives_class s_nm_eq scc sc_exists in
          let class_exists := CP.cert_classpool_names sc_exists in
          let sub_class_ok := ex_intro (P2 sc) s_nm (conj s_nm_eq (fixed_sub_class_refl sc_exists)) in
          Some (pack2 P sc meth (conj class_exists (conj meth_exists (conj is_class sub_class_ok))))
       | inright _ =>
          match method_lookup_super_classes classes (C.class_super_class sc) m d (CP.super_class_chain_inv sc_exists s_nm_eq scc) with
          | None => None
          | Some (pack2 c meth (conj c_exists (conj meth_exists (conj is_class sub_class_proof)))) =>
             let sub_class_proof' := fixed_sub_class_step sc_exists sub_class_proof in
             Some (pack2 P c meth (conj c_exists (conj meth_exists (conj is_class (ex_intro (P2 c) s_nm (conj s_nm_eq sub_class_proof'))))))
          end
       end
    | inright not_there =>
       let not_not_there := CP.super_class_chain_not_not_there s_nm_eq scc in
       match not_not_there not_there with end
    end
 | inright _ =>
    None
 end.

Lemma fixed_cl_impls_super : forall classes nm c x,
  CP.class_loaded classes nm c ->
  (exists s_nm, C.class_super_class c = Some s_nm /\ A.class_implements classes s_nm x) ->
  A.class_implements classes nm x.
intros. destruct H0 as [s_nm [c_super_s s_impl_x]]. eauto using A.cl_impls_super.
Save.
Implicit Arguments fixed_cl_impls_super [classes nm c x].

Definition resolve_method : forall (caller target:B.Classname.t) (m:B.Methodname.t) (d:C.descriptor) classes preclasses,
 {LOAD classes,preclasses ~~> classes' & p : C.class * C.method |
    class_loaded classes' (C.class_name (fst p)) (fst p) /\
    C.MethodList.lookup (C.class_methods (fst p)) (m,d) = Some (snd p) /\
    A.assignable classes' (C.ty_obj target) (C.ty_obj (C.class_name (fst p))) }
 :=
 fun caller target m d classes preclasses =>
 let P := fun classes' p => CP.class_loaded classes' (C.class_name (fst p)) (fst p) /\
                            C.MethodList.lookup (C.class_methods (fst p)) (m,d) = Some (snd p) /\
                            A.assignable classes' (C.ty_obj target) (C.ty_obj (C.class_name (fst p)))
 in
 match resolve_class caller target classes preclasses with
 | load_ok classes' preserved only_add c c_exists =>
    let c_exists' := cert_classpool_names c_exists in
    match BoolExt.bool_informative (C.class_interface c) with
    | left is_interface =>
       load_err P preserved only_add errIncompatibleClassChange
    | right is_class =>
       match C.MethodList.lookup_informative (C.class_methods c) (m,d) with
       | inleft (exist meth meth_exists) =>
          let sub_class_proof := fixed_sub_class_refl c_exists in
          let assignable_proof := A.assignable_class_class c_exists c_exists' is_class is_class sub_class_proof in
          load_ok P preserved only_add (c,meth) (conj c_exists' (conj meth_exists assignable_proof))
       | inright _ =>
          let scc := CP.cert_classpool_gives_scc c_exists' is_class in
           match method_lookup_super_classes classes' (C.class_super_class c) m d scc  with
           | Some (pack2 class meth (conj class_exists (conj meth_exists (conj is_class2 sub_class_proof)))) =>
              (* FIXME: check access permissions and that abstractness is correct *)
              let sub_class_proof' := fixed_sub_class_step c_exists sub_class_proof in
              let assignable_proof := A.assignable_class_class c_exists class_exists is_class is_class2 sub_class_proof' in
              load_ok P preserved only_add (class,meth) (conj class_exists (conj meth_exists assignable_proof))
           | None =>
              match method_lookup_all_interfaces classes' (C.class_super_class c) m d scc with
              | Some (pack2 class meth (conj class_exists (conj meth_exists (conj is_interface implements_proof)))) =>
                 let implements_proof' := fixed_cl_impls_super c_exists implements_proof in
                 let assignable_proof := A.assignable_class_interface2 c_exists class_exists is_class is_interface implements_proof' in
                 load_ok P preserved only_add (class,meth) (conj class_exists (conj meth_exists assignable_proof))
              | None =>
                 load_err P preserved only_add errNoSuchMethod
              end
           end
       end
    end
 | load_err classes' preserved only_add e =>
    load_err P preserved only_add e
 end.

(* Interface method resolution *)

Lemma fix_assignable : forall classes nmA nmB,
  nmA = nmB ->
  A.assignable classes (C.ty_obj nmA) (C.ty_obj nmA) ->
  A.assignable classes (C.ty_obj nmB) (C.ty_obj nmA).
intros. subst. assumption.
Save.
Implicit Arguments fix_assignable [classes nmA nmB].

Definition resolve_interface_method (caller:B.Classname.t)
                                    (target:B.Classname.t)
                                    (m:B.Methodname.t)
                                    (d:C.descriptor)
                                    (classes:cert_classpool)
                                    (preclasses:Preclasspool.t)
                                  : {LOAD classes,preclasses ~~> classes' & p : C.class * C.method |
                                       class_loaded classes' (C.class_name (fst p)) (fst p) /\
                                       C.MethodList.lookup (C.class_methods (fst p)) (m,d) = Some (snd p) /\
                                       A.assignable classes' (C.ty_obj target) (C.ty_obj (C.class_name (fst p))) }
 :=
 let P := fun classes' p => CP.class_loaded classes' (C.class_name (fst p)) (fst p) /\
                            C.MethodList.lookup (C.class_methods (fst p)) (m,d) = Some (snd p) /\
                            A.assignable classes' (C.ty_obj target) (C.ty_obj (C.class_name (fst p)))
 in
 match resolve_class caller target classes preclasses with
 | load_ok classes' preserved only_add c c_exists =>
    let c_exists' := cert_classpool_names c_exists in
    match BoolExt.bool_informative (C.class_interface c) with
    | left is_interface =>
       match C.MethodList.lookup_informative (C.class_methods c) (m,d) with
       | inleft (exist meth meth_exists) =>
          let assignable_proof := fix_assignable (cert_classpool_names_2 c_exists) (A.assignable_interface_interface_refl c_exists' is_interface) in
          load_ok P preserved only_add (c,meth) (conj c_exists' (conj meth_exists assignable_proof))
       | inright _ =>
          let gil := CP.cert_classpool_gives_gil2 c_exists in
          match method_lookup_interfaces classes' (C.class_interfaces c) m d gil with
          | Some (pack2 class meth (conj class_exists (conj meth_exists (conj is_interface2 implements_proof)))) =>
             let assignable_proof := A.assignable_interface_interface_strict c_exists class_exists is_interface is_interface2 implements_proof in
             load_ok P preserved only_add (class,meth) (conj class_exists (conj meth_exists assignable_proof))
          | None =>
             load_err P preserved only_add errNoSuchMethod
          end
       end
    | right is_class =>
       load_err P preserved only_add errIncompatibleClassChange
    end
 | load_err classes' preserved only_add e =>
    load_err P preserved only_add e
 end.

(* Field Resolution *)

Definition check_field_access : B.Classname.t -> C.class -> C.field -> option CP.exn :=
  fun caller c f => None.

Fixpoint field_lookup_interfaces (classes:CP.cert_classpool)
                                 (interfaces:list B.Classname.t)
                                 (f_nm:B.Fieldname.t)
                                 (t:C.java_type)
                                 (gil:good_interface_list2 classes interfaces)
                                 {struct gil}
                               : option { c : C.class, f : C.field |
                                          CP.class_loaded classes (C.class_name c) c /\
                                          C.FieldList.lookup (C.class_fields c) (f_nm,t) = Some f }
 :=
 let P := fun c f => CP.class_loaded classes (C.class_name c) c /\
                     C.FieldList.lookup (C.class_fields c) (f_nm,t) = Some f
 in
 match list_informative interfaces with
 | inleft (existS nmI (exist rest e)) =>
    match CP.class_loaded_dec classes nmI with
    | inleft (exist cI I_exists) =>
       match C.FieldList.lookup_informative (C.class_fields cI) (f_nm,t) with
       | inleft (exist f f_exists) =>
          let I_exists := CP.cert_classpool_names I_exists in
          Some (pack2 P cI f (conj I_exists f_exists))
       | inright _ =>
          let gil_super := CP.good_interface_list2_inv_1 gil e I_exists in
          match field_lookup_interfaces classes (C.class_interfaces cI) f_nm t gil_super with
          | Some x => Some x
          | None =>
             let gil_rest := CP.good_interface_list2_inv_2 gil e in
             field_lookup_interfaces classes rest f_nm t gil_rest
          end
       end
    | inright not_there =>
       let not_not_there := CP.good_interface_list2_not_not_there gil e in
       match not_not_there not_there with end
    end
 | inright _ =>
    None
 end.

Fixpoint field_lookup_super_classes (classes:CP.cert_classpool)
                                    (nm:option B.Classname.t)
                                    (f_nm:B.Fieldname.t)
                                    (t:C.java_type)
                                    (scc:super_class_chain classes nm)
                                    {struct scc}
                                  : option { c : C.class, f : C.field | CP.class_loaded  classes (C.class_name c) c /\ C.FieldList.lookup (C.class_fields c) (f_nm,t) = Some f }
 :=
 let P := fun c f => CP.class_loaded classes (C.class_name c) c /\ C.FieldList.lookup (C.class_fields c) (f_nm,t) = Some f in
 match option_informative nm with
 | inleft (exist s_nm s_nm_eq) =>
    let not_not_there := CP.super_class_chain_not_not_there s_nm_eq scc in
    match CP.class_loaded_dec classes s_nm with
    | inleft (exist sc sc_exists) =>
       match C.FieldList.lookup_informative (C.class_fields sc) (f_nm,t) with
       | inleft (exist f f_exists) =>
          Some (pack2 P sc f (conj (cert_classpool_names sc_exists) f_exists))
       | inright _ =>
          let gil := CP.cert_classpool_gives_gil2 sc_exists in
          match field_lookup_interfaces classes (C.class_interfaces sc) f_nm t gil with
          | Some x => Some x
          | None =>
             let scc_super := super_class_chain_inv sc_exists s_nm_eq scc in
             field_lookup_super_classes classes (C.class_super_class sc) f_nm t scc_super
          end
       end
    | inright not_there =>
       match not_not_there not_there with end
    end
 | inright _ =>
    None
 end.

Definition resolve_field : forall (caller target:B.Classname.t) (f_nm:B.Fieldname.t) (j_ty:C.java_type) classes preclasses,
 {LOAD classes,preclasses ~~> classes' & p : C.class * C.field |
   class_loaded classes' (C.class_name (fst p))  (fst p) /\
   C.FieldList.lookup (C.class_fields (fst p)) (f_nm,j_ty) = Some (snd p) }
 :=
 fun caller target f_nm j_ty classes preclasses =>
 let P := fun classes' p =>
            CP.class_loaded classes' (C.class_name (fst p)) (fst p) /\
            C.FieldList.lookup (C.class_fields (fst p)) (f_nm,j_ty) = Some (snd p) in
 match resolve_class caller target classes preclasses with
 | load_ok classes' preserved only_add c c_exists =>
    let c_exists := cert_classpool_names c_exists in
    match C.FieldList.lookup_informative (C.class_fields c) (f_nm, j_ty) with
    | inleft (exist f f_exists) =>
       (* FIXME: check access permissions *)
       load_ok P preserved only_add (c,f) (conj c_exists f_exists)
    | inright _ =>
       let gil := CP.cert_classpool_gives_gil2 c_exists in
       match field_lookup_interfaces classes' (C.class_interfaces c) f_nm j_ty gil with
       | Some (pack2 class f H) =>
          (* FIXME: check access permissions *)
          load_ok P preserved only_add (class,f) H
       | None =>
          match BoolExt.bool_informative (C.class_interface c) with
          | left is_interface =>
             (* assume that java.lang.Object has no fields *)
             load_err P preserved only_add errNoSuchField
          | right is_class =>
             let scc := CP.cert_classpool_gives_scc c_exists is_class in
             match field_lookup_super_classes classes' (C.class_super_class c) f_nm j_ty scc with
             | Some (pack2 class f H) =>
                (* FIXME: check access permissions *)
                load_ok P preserved only_add (class,f) H
             | None =>
                load_err P preserved only_add errNoSuchField
             end
          end
       end
    end
 | load_err classes' preserved only_add e =>
    load_err P preserved only_add e
 end.

(* Preservation of resolvability *)

Lemma preserve_resolve_class : forall caller target classesA classesA' classesB preclasses (p:preserve_old_classes classesA classesA') o c c_ex,
 resolve_class caller target classesA preclasses = load_ok _ p o c c_ex ->
 preserve_old_classes classesA classesB ->
 only_add_from_preclasses classesA classesB preclasses ->
 exists classesB', exists pB : preserve_old_classes classesB classesB', exists oB, exists c_exB,
   resolve_class caller target classesB preclasses = load_ok _ pB oB c c_exB
   /\ preserve_old_classes classesA' classesB'
   /\ only_add_from_preclasses classesA' classesB' preclasses.
unfold resolve_class. intros. 
destruct (CP.loader_dec (P:=fun classes c => CP.class_loaded classes target c)
                        (load_and_resolve_aux target preclasses (Preclasspool.all_wf_removals preclasses) classesA));
  destruct H2; destruct H2; destruct H2; destruct H2.
 (* load succeeded *)
 destruct H2. rewrite H2 in H. 
 destruct (option_dec (check_class_access caller x2)) as [[e check_res]|check_res]; rewrite check_res in H.
  (* access check failed *)
  discriminate.
  (* access check succeeded *)
  inversion H. subst.
  destruct (preserve_load_and_resolve_aux preclasses (Preclasspool.all_wf_removals preclasses) preclasses target classesA classesB classesA' x0 x1 c x3)
    as [classesB' [preserved2 [only_add2 [c_exists2 [H4 [H5 H6]]]]]]; auto.
   exact (fun _ _ x => x).
  rewrite H4. rewrite check_res. intuition eauto 9.
 (* load failed *)
 rewrite H2 in H. discriminate.
Save.
Implicit Arguments preserve_resolve_class [caller target classesA classesA' classesB preclasses p o c c_ex].

Lemma preserve_method_lookup_interfaces_failure : forall m d classesA classesB nm gilA gilB,
  method_lookup_interfaces classesA nm m d gilA = None ->
  preserve_old_classes classesA classesB ->
  method_lookup_interfaces classesB nm m d gilB = None.
intros m d classesA classesB nm gilA.
elim gilA using good_interface_list2_induction; simpl; intros.
(* base case *)
rewrite (gil2_inv_nil gilB). simpl. reflexivity.
(* step case *)
destruct (gil2_inv_cons gilB) as [i2 [i2_exists [i2_interface [step1 [step2 gilB_eq]]]]]. rewrite gilB_eq. simpl.
destruct (CP.class_loaded_dec classes i_nm) as [[cA cA_exists] | no_cA].
 (* Class was found, as it must be *)
 pose (cA_exists_in_B:=H2 _ _ cA_exists).
 simpl in cA_exists_in_B.
 destruct (CP.class_loaded_dec classesB i_nm) as [[cB cB_exists] | no_cB].
  (* lookup succeeded in classesB, as it must *)
  generalize cA_exists H1. rewrite (CP.class_loaded_unique cA_exists_in_B cB_exists) in *. clear cA cA_exists cA_exists_in_B H1. intros.
  destruct (C.MethodList.lookup_informative (C.class_methods cB) (m,d)) as [[methA methA_exists] | no_methA].
   (* method lookup succeeded, which is impossible *)
   discriminate.
   (* method lookup failed, so we examine the supers *)
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* succeeded in supers: impossible *)
    rewrite lookup_eq in H1. destruct lookup_result as [cI meth [X [Y [Z Z2]]]]. discriminate.
    (* failed in supers, try the siblings *)
    rewrite lookup_fail in H1.
    match goal with |- match method_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _ => set (gilB':=x) end.
    rewrite (H _ _ gilB' lookup_fail H2). clear lookup_fail H gilB'.
    match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
     (* method lookup succeeded in the siblings, which is impossible *)
     rewrite lookup_eq in H1. destruct lookup_result as [cI meth [X [Y [Z Z2]]]]. discriminate.
     (* method lookup failed in siblings *)
     match goal with |- match method_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _ => set (gilB':=x) end.
     rewrite (H0 gilB' lookup_fail H2). reflexivity.
  (* lookup failed in classesB: impossible *)
  elimtype False. apply no_cB. eauto.
 (* lookup failed in classesA: impossible *)
 elimtype False. apply no_cA. eauto.
Qed.
Implicit Arguments preserve_method_lookup_interfaces_failure [m d classesA classesB nm gilA].

Lemma preserve_method_lookup_interfaces : forall m d classesA classesB nm gilA gilB clazz meth HA,
  method_lookup_interfaces classesA nm m d gilA = Some (pack2 _ clazz meth HA) ->
  preserve_old_classes classesA classesB ->
  exists HB,
   method_lookup_interfaces classesB nm m d gilB = Some (pack2 _ clazz meth HB).
intros m d classesA classesB nm gilA.
elim gilA using good_interface_list2_induction; simpl; intros.
(* base case *)
discriminate.
(* step case *)
destruct (gil2_inv_cons gilB) as [i2 [i2_exists [i2_interface [step1 [step2 gilB_eq]]]]]. rewrite gilB_eq. simpl.
destruct (CP.class_loaded_dec classes i_nm) as [[cA cA_exists] | no_cA].
 (* lookup originally succeed *)
 pose (cA_exists_in_B:=H2 _ _ cA_exists).
 destruct (CP.class_loaded_dec classesB i_nm) as [[cB cB_exists] | no_cB].
  (* lookup succeeded in classesB, as we thought it would *)
  generalize cA_exists H1. rewrite (CP.class_loaded_unique cA_exists_in_B cB_exists) in *. clear cA cA_exists cA_exists_in_B H1. intros.
  destruct (C.MethodList.lookup_informative (C.class_methods cB) (m,d)) as [[methA methA_exists] | no_methA].
   (* Method lookup originally succeeded in this class *)
   inversion H1. subst cB methA.
   match goal with |- ex (fun _ => Some (pack2 _ _ _ ?HB) = _) => exists HB; reflexivity end.
   (* Method lookup failed in this interface and we had to look at the rest *)
   match goal with |- ex (fun _ => match method_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _) => set (gilB':=x) end.
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* lookup in super interfaces succeeded *)
    rewrite lookup_eq in H1.
    destruct lookup_result as [c' meth' [c'_exists [meth'_Exists [is_interface implements_proof]]]].
    inversion H1. subst c' meth'.
    destruct (H cB _ gilB' _ _ _ lookup_eq) as [super_HB super_lookup_ok]; eauto.
    rewrite super_lookup_ok. case super_HB. intros. case a. intros. case a0. intros.
    eapply ex_intro. reflexivity.
    (* lookup in super interfaces failed, try lookup in sibling interfaces *)
    rewrite lookup_fail in H1.
    rewrite (preserve_method_lookup_interfaces_failure gilB' lookup_fail H2).
    clear lookup_fail H.
    destruct (option_dec (method_lookup_interfaces classes rest m d g0)) as [[lookup_result lookup_eq] | lookup_fail].
     (* lookup in siblings succeeded *)
     rewrite lookup_eq in H1.
     destruct lookup_result as [c' meth' [c'_exists [meth'_exists [is_interface implements_proof]]]].
     inversion H1. subst c' meth'.
     destruct (H0 step2 _ _ _ lookup_eq) as [rest_HB rest_lookup_ok]; eauto.
     rewrite rest_lookup_ok. case rest_HB. intros. case a. intros. case a0. intros.
     eapply ex_intro. reflexivity.
     (* lookup in siblings failed: impossible *)
     rewrite lookup_fail in H1. discriminate.
  (* lookup failed in classesB *)
  elimtype False. apply no_cB. eauto.
 (* lookup failed in classesA *)
 elimtype False. apply no_cA. eauto.
Save.
Implicit Arguments preserve_method_lookup_interfaces [m d classesA classesB nm gilA clazz meth HA].

Lemma preserve_method_lookup_all_interfaces : forall m d classesA classesB nm sccA sccB clazz meth HA,
  method_lookup_all_interfaces classesA nm m d sccA = Some (pack2 _ clazz meth HA) ->
  preserve_old_classes classesA classesB ->
  exists HB,
    method_lookup_all_interfaces classesB nm m d sccB = Some (pack2 _ clazz meth HB).
intros m d classesA classesB nm sccA. 
elim sccA using super_class_chain_induction; simpl; intros.
(* base case *)
discriminate.
(* step case *)
destruct (scc_Some _ _ sccB) as [c2 [c2_exists [c2_class [s2 eq]]]]. rewrite eq. simpl. 
destruct (CP.class_loaded_dec classesA nm0) as [[cA cA_exists] | no_cA].
 (* lookup originally succeeded, as it must *)
 pose (cA_exists_in_B:=H1 _ _ cA_exists). 
 destruct (CP.class_loaded_dec classesB nm0) as [[cB cB_exists] | no_cB].
  (* lookup succeeded in classesB, as it must *)
  generalize cA_exists H0. rewrite (CP.class_loaded_unique cA_exists_in_B cB_exists) in *. clear cA cA_exists cA_exists_in_B H0. intros.
  match goal with |- ex (fun _ => match method_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _) => set (gilB':=x) end.
  match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
   (* lookup in these interfaces succeeded *)
   destruct lookup_result as [c' meth' [I_exists [meth_exists [is_interface dsi_evidence]]]].
   rewrite lookup_eq in H0. inversion H0. subst.
   destruct (preserve_method_lookup_interfaces gilB' lookup_eq H1) as [HB' eq']. rewrite eq'.
   case HB'. intros. case a. intros. case a0. intros.
   eapply ex_intro. reflexivity.
   (* lookup in these interfaces failed *)
   rewrite lookup_fail in H0.
   rewrite (preserve_method_lookup_interfaces_failure gilB' lookup_fail H1).
   clear lookup_fail.
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* lookup in super classes succeeded *)
    rewrite lookup_eq in H0.
    destruct lookup_result as [c' meth' [c'_exists [meth'_exists [is_interface dsi_evidence]]]].
    inversion H0. subst. clear H0.
    match goal with |- ex (fun _ => match method_lookup_all_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _) => set (sccB':=x) end.
    destruct (H cB _ sccB' _ _ _ lookup_eq H1) as [super_HB super_lookup_ok].
    rewrite super_lookup_ok. case super_HB. intros. case a. intros. case a0. intros.
    eapply ex_intro. reflexivity.
    (* lookup in super classes failed *)
    rewrite lookup_fail in H0. discriminate.
  (* lookup failed in classesB: impossible *)
  elimtype False. apply no_cB. eauto.
 (* lookup failed in classesA: impossible *)
 elimtype False. apply no_cA. eauto.
Qed.
Implicit Arguments preserve_method_lookup_all_interfaces [m d classesA classesB nm sccA clazz meth HA].

Lemma preserve_method_lookup_super_classes : forall m d classesA classesB nm sccA sccB clazz meth HA,
  method_lookup_super_classes classesA nm m d sccA = Some (pack2 _ clazz meth HA) ->
  preserve_old_classes classesA classesB ->
  exists HB,
    method_lookup_super_classes classesB nm m d sccB = Some (pack2 _ clazz meth HB).
intros m d classesA classesB nm sccA.
elim sccA using super_class_chain_induction; simpl; intros.

(* base case *)
discriminate.

(* step case *)
destruct (scc_Some _ _ sccB) as [c2 [c2_exists [c2_class [s2 eq]]]]. rewrite eq. simpl. 
destruct (CP.class_loaded_dec classesA nm0) as [[cA cA_exists] | no_cA].
 (* lookup originally succeeded *)
 pose (cA_exists_in_B:=H1 _ _ cA_exists).
 destruct (CP.class_loaded_dec classesB nm0) as [[cB cB_exists] | no_cB].
  (* lookup succeeded in classesB, as we thought it would *)
  generalize cA_exists H0. rewrite (CP.class_loaded_unique cA_exists_in_B cB_exists) in *. clear cA cA_exists cA_exists_in_B H0. intros.
  destruct (C.MethodList.lookup_informative (C.class_methods cB) (m,d)) as [[methA methA_exists] | no_methA].
   (* Method lookup succeeded in this class *)
   inversion H0. subst cB methA.
   eapply ex_intro. reflexivity.
   (* Method lookup failed *)
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* lookup in the super classes succeeded *)
    rewrite lookup_eq in H0.
    destruct lookup_result as [c' meth' [c'_exists [meth'_exists [is_class sub_class_proof]]]].
    inversion H0. subst c' meth'.
    set (sccB':=(s2 cB (eq_ind_r (fun nm1 => CP.class_loaded classesB nm1 cB) cB_exists (refl_equal nm0)))).
    destruct (H cB _ sccB' _ _ _ lookup_eq) as [super_HB super_lookup_ok]; eauto.
    rewrite super_lookup_ok. case super_HB. intros. case a. intros. case a0. intros. 
    eapply ex_intro. reflexivity.

    (* lookup in the super classes failed: not possible *)
    rewrite lookup_fail in H0. discriminate. 
  (* class lookup failed in classesB, but this is unpossible *)
  elimtype False. apply no_cB. eauto.
 (* lookup originally failed. Again, this is unpossible *)
 elimtype False. apply no_cA. eauto.
Qed.
Implicit Arguments preserve_method_lookup_super_classes [m d classesA classesB nm sccA clazz meth HA].

Lemma preserve_method_lookup_super_classes_failure : forall m d classesA classesB nm sccA sccB,
  method_lookup_super_classes classesA nm m d sccA = None ->
  preserve_old_classes classesA classesB ->
  method_lookup_super_classes classesB nm m d sccB = None.
intros m d classesA classesB nm sccA.
elim sccA using super_class_chain_induction; simpl; intros.
(* base case *)
rewrite (scc_None _ sccB). reflexivity.
(* step case *)
destruct (scc_Some _ _ sccB) as [c2 [c2_exists [c2_class [s2 eq]]]]. rewrite eq. simpl.
destruct (CP.class_loaded_dec classesA nm0) as [[cA cA_exists] | no_cA].
 (* class exists in A, as it must *)
 pose (cA_exists_in_B:=H1 _ _ cA_exists).
 destruct (CP.class_loaded_dec classesB nm0) as [[cB cB_exists] | no_cB].
  (* exists in B, as it must *)
  generalize cA_exists H0. rewrite (CP.class_loaded_unique cA_exists_in_B cB_exists) in *. clear cA cA_exists cA_exists_in_B H0. intros.
  destruct (C.MethodList.lookup_informative (C.class_methods cB) (m,d)) as [[meth meth_exists] | no_meth].
   (* method exists, impossible *)
   discriminate.
   (* method doesn't exist here *)
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* lookup in super classes succeeded: impossible *)
    rewrite lookup_eq in H0. destruct lookup_result as [c' meth' [c'_exists [meth'_exists [is_class sub_class_proof]]]]. discriminate.
    (* lookup failed in super classes, as we expect *)
    match goal with |- match method_lookup_super_classes _ _ _ _ ?x with Some _ => _ | None => _ end = _ => set (sccB':=x) end.
    rewrite (H _ _ sccB' lookup_fail H1).
    reflexivity.
  (* not exists in B, impossible *)
  elimtype False. apply no_cB. eauto.
 (* not exists in A, impossible *)
 elimtype False. apply no_cA. eauto.
Qed.
Implicit Arguments preserve_method_lookup_super_classes_failure [m d classesA classesB nm sccA].

Lemma preserve_resolve_method : forall caller nm m d classesA classesA' classesB preclasses p o cm HA,
  resolve_method caller nm m d classesA preclasses = load_ok _ (classes':=classesA') p o cm HA ->
  preserve_old_classes classesA classesB ->
  only_add_from_preclasses classesA classesB preclasses ->
  exists classesB', exists pB, exists oB, exists HB,
  resolve_method caller nm m d classesB preclasses = load_ok _ (classes':=classesB') pB oB cm HB.
unfold resolve_method. intros.
destruct (loader_dec (P:=fun classes c => CP.class_loaded classes nm c)
           (resolve_class caller nm classesA preclasses))
      as [[classes' [preserved [only_add [res_c [Hres res_eq]]]]] | [classes' [preserved [only_add [e res_eq]]]]].
 (* resolution of the class succeeded *)
 destruct (preserve_resolve_class res_eq H0 H1) as [classesB' [pB [oB [c_exB [res_eq2 [p2 o2]]]]]].
 rewrite res_eq in H. rewrite res_eq2.
 destruct (BoolExt.bool_informative (C.class_interface res_c)).
  (* The resolved class was (and is) an interface *)
  discriminate.
  (* The resolved class was (and is) really a class *)
  destruct (C.MethodList.lookup_informative (C.class_methods res_c) (m,d)) as [[meth meth_exists] | no_meth].
   (* Method lookup succeeded both times *)
   inversion H. subst. exists classesB'. exists pB. exists oB.
   eapply ex_intro. reflexivity.
   (* Method lookup failed both times *)
   match goal with |- ex (fun _ => ex (fun _ => ex (fun _ => ex (fun _ => match method_lookup_super_classes _ _ _ _ ?x with Some _ => _ | None => _ end = _)))) => set (sccB':=x) end.
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[[class' meth' super_HA] lookup_eq] | lookup_fail] end.
    (* Lookup in super classes succeeded *)
    destruct (preserve_method_lookup_super_classes sccB' lookup_eq p2) as [super_HB super_lookup_ok].
    rewrite super_lookup_ok. rewrite lookup_eq in H.
    clear lookup_eq.
    generalize H. clear H.
    case super_HA. intros e0 a. case a. intros e1 a0. case a0. intros. inversion H. subst. 
    case super_HB. intros. case a1. intros. case a2. intros.
    exists classesB'. exists pB. exists oB.
    eapply ex_intro. reflexivity.
    (* lookup in super classes failed *)
    rewrite lookup_fail in H. rewrite (preserve_method_lookup_super_classes_failure sccB' lookup_fail p2).
    clear lookup_fail.
    match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ =>
        destruct (option_dec v) as [[[class' meth' [class'_exists [meth'_exists [is_interface implements_proof]]]] lookup_eq] | lookup_fail] end.
     (* lookup in interfaces succeeded *)
     destruct (preserve_method_lookup_all_interfaces sccB' lookup_eq p2) as [super_HB super_lookup_ok].
     rewrite lookup_eq in H. rewrite super_lookup_ok.
     inversion H. subst. case super_HB. intros. case a. intros. case a0. intros.
     exists classesB'. exists pB. exists oB. 
     eapply ex_intro. reflexivity.
     (* lookup in interfaces failed: impossible *)
     rewrite lookup_fail in H. discriminate.
 (* class resolution failed *)
 rewrite res_eq in H. discriminate. 
Save.

Lemma preserve_resolve_interface_method : forall caller nm m d classesA classesA' classesB preclasses p o cm HA,
  resolve_interface_method caller nm m d classesA preclasses = load_ok _ (classes':=classesA') p o cm HA ->
  preserve_old_classes classesA classesB ->
  only_add_from_preclasses classesA classesB preclasses ->
  exists classesB', exists pB, exists oB, exists HB,
  resolve_interface_method caller nm m d classesB preclasses = load_ok _ (classes':=classesB') pB oB cm HB.
unfold resolve_interface_method. intros.
destruct (loader_dec (P:=fun classes c => CP.class_loaded classes nm c)
           (resolve_class caller nm classesA preclasses))
      as [[classes' [preserved [only_add [res_c [Hres res_eq]]]]] | [classes' [preserved [only_add [e res_eq]]]]].
 (* resolution of the class succeeded *)
 destruct (preserve_resolve_class res_eq H0 H1) as [classesB' [pB [oB [c_exB [res_eq2 [p2 o2]]]]]].
 rewrite res_eq in H. rewrite res_eq2.
 destruct (BoolExt.bool_informative (C.class_interface res_c)).
  (* The resolved class was (and is) an interface *)
  destruct (C.MethodList.lookup_informative (C.class_methods res_c) (m,d)) as [[meth meth_exists] | no_meth].
   (* Method lookup succeeded both times *)
   inversion H. subst. exists classesB'. exists pB. exists oB. eapply ex_intro. reflexivity.
   (* Method lookup failed both times *)
   match goal with |- ex (fun _ => ex (fun _ => ex (fun _ => ex (fun _ => match method_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _)))) => set (gilB':=x) end.
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ =>
       destruct (option_dec v) as [[[class' meth' [class'_exists [meth'_exists [is_interface implements_proof]]]] lookup_eq] | lookup_fail] end.
    (* Lookup in super classes succeeded *)
    destruct (preserve_method_lookup_interfaces gilB' lookup_eq p2) as [super_HB super_lookup_ok].
    rewrite super_lookup_ok. rewrite lookup_eq in H.
    clear lookup_eq.
    inversion H. subst. case super_HB. intros. case a. intros. case a0. intros.
    exists classesB'. exists pB. exists oB. eapply ex_intro. reflexivity.
    (* lookup in super classes failed *)
    rewrite lookup_fail in H. discriminate. 
  (* The resolved class was (and is) a class *)
  discriminate.
 (* class resolution failed *)
 rewrite res_eq in H. discriminate. 
Save.

Lemma preserve_field_lookup_interfaces_failure : forall f_nm f_ty classesA classesB interfaces gilA gilB,
  field_lookup_interfaces classesA interfaces f_nm f_ty gilA = None ->
  preserve_old_classes classesA classesB ->
  field_lookup_interfaces classesB interfaces f_nm f_ty gilB = None.
intros f_nm f_ty classesA classesB interfaces gilA.
elim gilA using good_interface_list2_induction; simpl; intros.
(* base case *)
rewrite (gil2_inv_nil gilB). reflexivity.
(* step case *)
destruct (gil2_inv_cons gilB) as [i2 [i2_exists [i2_interface [step1 [step2 gilB_eq]]]]]. rewrite gilB_eq. simpl.
destruct (CP.class_loaded_dec classes i_nm) as [[cA cA_exists] | no_cA].
 (* class exists in A, as it must *)
 pose (cA_exists_inB:=H2 _ _ cA_exists).
 destruct (CP.class_loaded_dec classesB i_nm) as [[cB cB_exists] | no_cB].
  (* class exists in B, as it must *)
  generalize cA_exists H1. rewrite (CP.class_loaded_unique cA_exists_inB cB_exists) in *. clear cA cA_exists cA_exists_inB H1. intros. 
  destruct (C.FieldList.lookup_informative (C.class_fields cB) (f_nm,f_ty)) as [[f f_exists] | no_f].
   (* field exists: impossible *)
   discriminate.
   (* field doesn't exist here *)
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* super lookup succeeded: impossible *)
    rewrite lookup_eq in H1. discriminate.
    (* super lookup failed: trying the rest *)
    rewrite lookup_fail in H1.
    match goal with |- match field_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _ => set (gilB':=x) end.
    rewrite (H _ _ gilB' lookup_fail H2).
    apply H0; assumption.
  (* no class in B: impossible *)
  elimtype False. apply no_cB. eauto.
 (* no class in A: impossible *)
 elimtype False. apply no_cA. eauto.
Qed.
Implicit Arguments preserve_field_lookup_interfaces_failure [f_nm f_ty classesA classesB interfaces gilA].

Lemma preserve_field_lookup_interfaces : forall f_nm f_ty classesA classesB interfaces gilA gilB c f HA,
  field_lookup_interfaces classesA interfaces f_nm f_ty gilA = Some (pack2 _ c f HA) ->
  preserve_old_classes classesA classesB ->
  exists HB,
    field_lookup_interfaces classesB interfaces f_nm f_ty gilB = Some (pack2 _ c f HB).
intros f_nm f_ty classesA classesB interfaces gilA.
elim gilA using good_interface_list2_induction; simpl; intros.
(* base case *)
discriminate.
(* step case *)
destruct (gil2_inv_cons gilB) as [i2 [i2_exists [i2_interface [step1 [step2 gilB_eq]]]]]. rewrite gilB_eq. simpl.
destruct (CP.class_loaded_dec classes i_nm) as [[cA cA_exists] | no_cA].
 (* class exists in A, as it must *)
 pose (cA_exists_inB:=H2 _ _ cA_exists).
 destruct (CP.class_loaded_dec classesB i_nm) as [[cB cB_exists] | no_cB].
  (* class exists in B, as it must *)
  generalize cA_exists H1. rewrite (CP.class_loaded_unique cA_exists_inB cB_exists) in *. clear cA cA_exists cA_exists_inB H1. intros.
  destruct (C.FieldList.lookup_informative (C.class_fields cB) (f_nm,f_ty)) as [[f' f'_exists] | no_f'].
   (* field existed in this class *)
   inversion H1. subst.
   eapply ex_intro. reflexivity.
   (* no such field in this class *)
   match goal with |- ex (fun _ => match field_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _) => set (gilB':=x) end.
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* lookup in super interfaces succeeded *)
    rewrite lookup_eq in H1.
    destruct lookup_result as [c' f' [c'_exists f'_exists]].
    inversion H1. subst.
    destruct (H cB _ gilB' _ _ _ lookup_eq H2) as [super_HB super_lookup_ok].
    rewrite super_lookup_ok. exists super_HB. reflexivity.
    (* lookup in super interfaces failed *)
    rewrite lookup_fail in H1. rewrite (preserve_field_lookup_interfaces_failure gilB' lookup_fail H2).
    clear lookup_fail gilB'.
    apply (H0 step2 _ _ _ H1 H2).
  (* class not in B: impossible *)
  elimtype False. apply no_cB. eauto.
 (* class not in A: impossible *)
 elimtype False. apply no_cA. eauto.
Qed.
Implicit Arguments preserve_field_lookup_interfaces [f_nm f_ty classesA classesB interfaces gilA c f HA].

Lemma preserve_field_lookup_super_classes : forall f_nm f_ty classesA classesB nm sccA sccB c f HA,
  field_lookup_super_classes classesA nm f_nm f_ty sccA = Some (pack2 _ c f HA) ->
  preserve_old_classes classesA classesB ->
  exists HB,
    field_lookup_super_classes classesB nm f_nm f_ty sccB = Some (pack2 _ c f HB).
intros f_nm f_ty classesA classesB nm sccA.
elim sccA using super_class_chain_induction; simpl; intros.

(* base case *)
discriminate.

(* step case *)
destruct (scc_Some _ _ sccB) as [c2 [c2_exists [c2_class [step scc_eq]]]]. rewrite scc_eq. simpl.
destruct (CP.class_loaded_dec classesA nm0) as [[cA cA_exists] | no_cA].
 (* lookup originally succeeded *)
 pose (cA_exists_in_B:=H1 _ _ cA_exists). 
 destruct (CP.class_loaded_dec classesB nm0) as [[cB cB_exists] | no_cB]. 
  (* lookup succeeded in classesB, as we thought it would *)
  generalize cA_exists H0. rewrite (CP.class_loaded_unique cA_exists_in_B cB_exists) in *. clear cA cA_exists cA_exists_in_B H0. intros.
  destruct (C.FieldList.lookup_informative (C.class_fields cB) (f_nm,f_ty)) as [[f' f'_exists] | no_f'].
   (* Field lookup succeeded in this class *)
   inversion H0. subst. eapply ex_intro. reflexivity.
   (* Method lookup failed here, try the super interfaces *)
   match goal with |- ex (fun _ => match field_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _) => set (gilB':=x) end.
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* succeeded in super interfaces *)
    rewrite lookup_eq in H0. destruct lookup_result as [c' f' HA']. inversion H0. subst.
    destruct (preserve_field_lookup_interfaces gilB' lookup_eq H1) as [interfaces_HB interfaces_lookup_ok].
    rewrite interfaces_lookup_ok. exists interfaces_HB. reflexivity.
    (* failed in super interfaces *)
    rewrite lookup_fail in H0. rewrite (preserve_field_lookup_interfaces_failure gilB' lookup_fail H1).
    eapply H; eauto.
  (* class lookup failed in classesB, but this is unpossible *)
  elimtype False. apply no_cB. eauto.
 (* lookup originally failed. Again, this is unpossible *)
 elimtype False. apply no_cA. eauto.
Save.
Implicit Arguments preserve_field_lookup_super_classes [f_nm f_ty classesA classesB nm sccA c f HA].

Lemma preserve_resolve_field : forall caller nm f_nm f_ty classesA classesA' classesB preclasses p o cf HA,
  resolve_field caller nm f_nm f_ty classesA preclasses = load_ok _ (classes':=classesA') p o cf HA ->
  preserve_old_classes classesA classesB ->
  only_add_from_preclasses classesA classesB preclasses ->
  exists classesB', exists pB, exists oB, exists HB,
  resolve_field caller nm f_nm f_ty classesB preclasses = load_ok _ (classes':=classesB') pB oB cf HB.
unfold resolve_field. intros. 
destruct (loader_dec (P:=fun classes c => CP.class_loaded classes nm c)
           (resolve_class caller nm classesA preclasses))
      as [[classes' [preserved [only_add [res_c [Hres res_eq]]]]] | [classes' [preserved [only_add [e res_eq]]]]].
 (* resolution of the class succeeded *)
 destruct (preserve_resolve_class res_eq H0 H1) as [classesB' [pB [oB [c_exB [res_eq2 [p2 o2]]]]]].
 rewrite res_eq in H. rewrite res_eq2.
 exists classesB'. exists pB. exists oB.
 destruct (C.FieldList.lookup_informative (C.class_fields res_c) (f_nm,f_ty)) as [[f' f'_exists] | no_f'].
  (* field was found here *)
  inversion H. subst.
  exists (conj (cert_classpool_names c_exB) f'_exists). reflexivity.
  (* field wasn't found in this class, try the super interfaces *)
   match goal with |- ex (fun _ => match field_lookup_interfaces _ _ _ _ ?x with Some _ => _ | None => _ end = _) => set (gilB':=x) end.
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
    (* succeeded in super interfaces *)
    rewrite lookup_eq in H. destruct lookup_result as [c' f' HA']. inversion H. subst.
    destruct (preserve_field_lookup_interfaces gilB' lookup_eq p2) as [interfaces_HB interfaces_lookup_ok].
    rewrite interfaces_lookup_ok. exists interfaces_HB. reflexivity.
    (* failed in super interfaces *)
    rewrite lookup_fail in H. rewrite (preserve_field_lookup_interfaces_failure gilB' lookup_fail p2).
    clear lookup_fail.
    destruct (BoolExt.bool_informative (C.class_interface res_c)) as [is_interface | is_class].
     (* is an interface: no super classes *)
     discriminate.
     (* is a class, so we check the super classes *)
     match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct (option_dec v) as [[lookup_result lookup_eq] | lookup_fail] end.
      (* it was found in the super classes or their interfaces *)
      rewrite lookup_eq in H. destruct lookup_result as [c' f' HA']. inversion H. subst.
      match goal with |- ex (fun _ => match field_lookup_super_classes _ _ _ _ ?x with Some _ => _ | None => _ end = _) => set (sccB':=x) end.
      destruct (preserve_field_lookup_super_classes sccB' lookup_eq p2) as [super_HB super_lookup_ok].
      rewrite super_lookup_ok. exists super_HB. reflexivity.
      (* wasn't found at all: impossible *)
      rewrite lookup_fail in H. discriminate.
 (* class resolution failed: impossible *)
 rewrite res_eq in H. discriminate.
Save.

End MkResolution.
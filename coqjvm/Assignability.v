Require Import ClasspoolIface.
Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import List.
Require Import BoolExt.
Require Import OptionExt.
Require Import AssignabilityIface.

Require Import AnnotationIface.

Module MkAssignability (B : BASICS)
                       (ANN : ANNOTATION B)
                       (C : CLASSDATATYPES B ANN)
                       (CP : CLASSPOOL B ANN C)
                     : ASSIGNABILITY B ANN C CP.

(* the assignability predicate *)

Inductive sub_class (classes:CP.cert_classpool) : B.Classname.t -> B.Classname.t -> Prop :=
| sub_class_refl : forall nm cwitness,
   CP.class_loaded classes nm cwitness ->
   sub_class classes nm nm
| sub_class_step : forall nm nm_t s_nm c,
   CP.class_loaded classes nm c ->
   C.class_super_class c = Some s_nm ->
   sub_class classes s_nm nm_t ->
   sub_class classes nm nm_t.

Inductive direct_super_interface (classes:CP.cert_classpool) : list B.Classname.t -> B.Classname.t -> Prop :=
| d_inter_here : forall nmT interfaces,
   direct_super_interface classes (nmT::interfaces) nmT
| d_inter_step_up : forall interfaces nmX cX nmT,
   CP.class_loaded classes nmX cX ->
   C.class_interface cX = true ->
   direct_super_interface classes (C.class_interfaces cX) nmT ->
   direct_super_interface classes (nmX::interfaces) nmT
| d_inter_step_along : forall interfaces nmT nmX,
   direct_super_interface classes interfaces nmT ->
   direct_super_interface classes (nmX::interfaces) nmT.

Definition class_implements classes nmS nmT :=
 exists nmS', exists cS',
   CP.class_loaded classes nmS' cS' /\
   C.class_interface cS' = false /\
   sub_class classes nmS nmS' /\
   direct_super_interface classes (C.class_interfaces cS') nmT.

Lemma cl_impls_direct : forall classes nmS cS nmT,
  CP.class_loaded classes nmS cS ->
  C.class_interface cS = false ->
  direct_super_interface classes (C.class_interfaces cS) nmT ->
  class_implements classes nmS nmT.
unfold class_implements. intuition eauto 8 using sub_class_refl.
Qed.

Lemma cl_impls_super: forall classes nmS cS nm_superS nmT,
  CP.class_loaded classes nmS cS ->
  C.class_super_class cS = Some nm_superS ->
  class_implements classes nm_superS nmT ->
  class_implements classes nmS nmT.
intros classes nmS cS nm_superS nmT loaded_nmS_cS cS_super super_impl_T. 
destruct super_impl_T as [nmS' [cS' [S'_loaded [S'_not_interface [S_S' S'_T]]]]].
unfold class_implements. intuition eauto 9 using sub_class_step.
Qed.

(* This is from the specification on page 278 of the JVM spec (except for arrays, for now) *)
Inductive assignable' (classes:CP.cert_classpool) : C.java_ref_type -> C.java_ref_type -> Prop :=
| assign_class_class : forall nmS nmT cS cT,
   CP.class_loaded classes nmS cS ->
   CP.class_loaded classes nmT cT ->
   C.class_interface cS = false ->
   C.class_interface cT = false ->
   sub_class classes nmS nmT ->
   assignable' classes (C.ty_obj nmS) (C.ty_obj nmT)
| assign_class_interface : forall nmS nmT cS cT nmS' cS',
   CP.class_loaded  classes nmS cS ->
   CP.class_loaded  classes nmT cT ->
   CP.class_loaded  classes nmS' cS' ->
   C.class_interface cS = false ->
   C.class_interface cS' = false ->
   C.class_interface cT = true ->
   sub_class classes nmS nmS' ->
   direct_super_interface classes (C.class_interfaces cS') nmT ->
   assignable' classes (C.ty_obj nmS) (C.ty_obj nmT)
| assign_interface_class : forall nmS cS,
   CP.class_loaded  classes nmS cS ->
   C.class_interface cS = true ->
   assignable' classes (C.ty_obj nmS) (C.ty_obj B.java_lang_Object)
| assign_interface_interface_refl : forall nmS cS,
   CP.class_loaded  classes nmS cS ->
   C.class_interface cS = true ->
   assignable' classes (C.ty_obj nmS) (C.ty_obj nmS)
| assign_interface_interface_strict : forall nmS nmT cS cT,
   CP.class_loaded  classes nmS cS ->
   CP.class_loaded  classes nmT cT ->
   C.class_interface cS = true ->
   C.class_interface cT = true ->
   direct_super_interface classes (C.class_interfaces cS) nmT ->
   assignable' classes (C.ty_obj nmS) (C.ty_obj nmT).
Definition assignable := assignable'.

Definition assignable_class_class := assign_class_class.
Definition assignable_class_interface := assign_class_interface.
Definition assignable_interface_class := assign_interface_class.
Definition assignable_interface_interface_refl := assign_interface_interface_refl.
Definition assignable_interface_interface_strict := assign_interface_interface_strict.

Lemma sub_class_trans : forall classes a b c,
  sub_class classes a b ->
  sub_class classes b c ->
  sub_class classes a c.
intros classes a b c. induction 1; eauto using sub_class_step.
Qed.

Lemma sub_class_linearish : forall classes A B C,
  sub_class classes A B ->
  sub_class classes A C ->
  sub_class classes B C \/ sub_class classes C B.
intros classes A B C A_sub_B A_sub_C.
induction A_sub_B as [A|A B A' cA A_exists A_sc_A' A'_sub_B].
 (* A = B *)
 left. assumption.
 (* A < B *)
 destruct A_sub_C as [C|A C A'' cA' A_exists' A_sc_A'' A''_sub_C].
  (* A = C *)
  right. clear H. eapply sub_class_step; eauto.
  (* A < C *)
  rewrite (CP.class_loaded_unique A_exists A_exists') in *.
  rewrite A_sc_A' in A_sc_A''. inversion A_sc_A''. subst.
  auto.
Qed.

Ltac clu_congruence :=
  match goal with
  | [H1 : CP.class_loaded _ _ _, H2 : CP.class_loaded _ _ _ |- _ ] => rewrite (CP.class_loaded_unique H1 H2) in *; clear H1 H2; first [ congruence | clu_congruence ]
  end.

Lemma get_sub_class : forall classes A B cA cB,
  CP.class_loaded  classes A cA ->
  CP.class_loaded  classes B cB ->
  C.class_interface cA = false ->
  C.class_interface cB = false ->
  assignable classes (C.ty_obj A) (C.ty_obj B) ->
  sub_class classes A B.
intros classes A B cA cB A_exists B_exists A_class B_class A_sub_B.
inversion A_sub_B; subst; clu_congruence.
Qed.

Lemma get_class_implements : forall classes A B cA cB,
  CP.class_loaded  classes A cA ->
  CP.class_loaded  classes B cB ->
  C.class_interface cA = false ->
  C.class_interface cB = true ->
  assignable classes (C.ty_obj A) (C.ty_obj B) ->
  exists A', exists cA', CP.class_loaded  classes A' cA'
                         /\ C.class_interface cA' = false
                         /\ sub_class classes A A'
                         /\ direct_super_interface classes (C.class_interfaces cA') B.
intros classes A B cA cB A_exists B_exists A_class B_interface A_sub_B.
inversion A_sub_B; subst; try clu_congruence. intuition eauto 6.
Qed.

Lemma assignable_shared_subclass : forall classes A B C cA cB cC,
  CP.class_loaded classes A cA ->
  CP.class_loaded classes B cB ->
  CP.class_loaded classes C cC ->
  C.class_interface cA = false ->
  C.class_interface cB = false ->
  C.class_interface cC = false ->
  assignable classes (C.ty_obj A) (C.ty_obj B) ->
  assignable classes (C.ty_obj A) (C.ty_obj C) ->
  assignable classes (C.ty_obj B) (C.ty_obj C) \/ assignable classes (C.ty_obj C) (C.ty_obj B).
intros classes A B C cA cB cC.
intros A_exists B_exists C_exists A_class B_class C_class.
intros A_sub_B. intros A_sub_C.
destruct (sub_class_linearish classes A B C).
 eapply get_sub_class; eassumption.
 eapply get_sub_class; eassumption.
 left. eapply assign_class_class; eassumption.
 right. eapply assign_class_class; eassumption.
Qed.

Lemma assignable_class_interface2 : forall classes nmS nmT cS cT,
  CP.class_loaded classes nmS cS ->
  CP.class_loaded classes nmT cT ->
  C.class_interface cS = false ->
  C.class_interface cT = true ->
  class_implements classes nmS nmT ->
  assignable classes (C.ty_obj nmS) (C.ty_obj nmT).
intros. destruct H3 as [nmS' [cS' [S'_loaded [S'_not_interface [S_S' S'_T]]]]].
eapply assign_class_interface; eassumption.
Qed.

Lemma assignable_shared_subclass_2 : forall classes A B C cA cB cC,
  CP.class_loaded classes A cA ->
  CP.class_loaded classes B cB ->
  CP.class_loaded classes C cC ->
  C.class_interface cA = false ->
  C.class_interface cB = false ->
  C.class_interface cC = true ->
  assignable classes (C.ty_obj A) (C.ty_obj B) ->
  assignable classes (C.ty_obj A) (C.ty_obj C) ->
     assignable classes (C.ty_obj B) (C.ty_obj C)
  \/ (exists B', exists cB', CP.class_loaded classes B' cB'
                             /\ C.class_interface cB' = false
                             /\ assignable classes (C.ty_obj B') (C.ty_obj B)
                             /\ assignable classes (C.ty_obj A) (C.ty_obj B')
                             /\ assignable classes (C.ty_obj B') (C.ty_obj C)).
intros classes A B C cA cB cC.
intros A_exists B_exists C_exists A_class B_class C_interface.
intros A_sub_B A_sub_C.
assert (A_subc_B:sub_class classes A B);[eapply get_sub_class; eassumption|].
destruct (get_class_implements classes A C cA cC) as [A' [cA' [A'_exists [A'_class [A_sub_A' dsi]]]]]; try assumption.
destruct (sub_class_linearish classes A B A' A_subc_B A_sub_A') as [B_sub_A' | A'_sub_B].
 (* B <: A' *)
 left. eapply assign_class_interface; eauto.
 (* A' <: B *)
 right. exists A'. exists cA'. intuition.
  eapply assign_class_class; eassumption.
  eapply assign_class_class; eassumption.
  eapply assign_class_interface; try eassumption. eapply sub_class_refl. apply A'_exists.
Qed.

Lemma sub_class_Object_top : forall classes nm c,
  CP.class_loaded  classes nm c ->
  C.class_interface c = false ->
  sub_class classes nm B.java_lang_Object.
intros classes nm c nm_c c_class. 
assert (scc:CP.super_class_chain classes (C.class_super_class c)) by eauto using CP.cert_classpool_gives_scc.
set (sc:=C.class_super_class c) in *.
set (e:=refl_equal sc : C.class_super_class c = sc). generalize sc scc nm c nm_c c_class e. clear sc scc nm c nm_c c_class e. intros sc scc.
elim scc using CP.super_class_chain_induction; clear scc; intros.
 (* top case: if a class is loaded and has no super class, then it is Object *)
 rewrite (CP.no_super_is_jlObject _ _ _ nm_c e). destruct (CP.cert_classpool_has_Object classes) as [objc [objloaded _]].  eapply sub_class_refl. apply objloaded.
 (* step case *)
 eauto using sub_class_step.
Qed.
(* FIXME: should we prohibit sub_class from ever relating interfaces? *)

Lemma assignable_Object : forall classes a c,
  CP.class_loaded  classes a c ->
  assignable classes (C.ty_obj a) (C.ty_obj B.java_lang_Object).
intros. destruct (bool_dec (C.class_interface c)). 
 (* it is an interface *)
 eapply assign_interface_class; eauto.
 (* it is a class *)
 destruct (CP.cert_classpool_has_Object classes) as [object [object_exists [_ [_ object_class]]]].  
 eapply assign_class_class; eauto. eapply sub_class_Object_top; eassumption. 
Qed.

Lemma sub_class_Object_only : forall classes a,
  sub_class classes B.java_lang_Object a -> a = B.java_lang_Object.
intros. inversion H.
 reflexivity.
 destruct (CP.cert_classpool_has_Object classes) as [object [object_exists [no_super _]]].
  rewrite (CP.class_loaded_unique object_exists H0) in *. rewrite H1 in no_super. discriminate.
Qed.

Lemma no_interfaces_no_direct_super_interface : forall classes a,
 ~(direct_super_interface classes nil a).
unfold not. intros. inversion H.
Qed.

Lemma assignable_Object_only : forall classes a,
  assignable classes (C.ty_obj B.java_lang_Object) a -> a = C.ty_obj B.java_lang_Object.
intros.
destruct (CP.cert_classpool_has_Object classes) as [object [object_exists [no_super [no_interfaces is_class]]]].
inversion H; try congruence.
 eapply (f_equal C.ty_obj). eapply sub_class_Object_only. apply H5.
 assert (nmS' = B.java_lang_Object) by (eapply sub_class_Object_only; eassumption).
  subst.
  rewrite (CP.class_loaded_unique object_exists H3) in *.
  rewrite no_interfaces in H8. elimtype False. apply (no_interfaces_no_direct_super_interface _ _ H8). 
 clu_congruence.
Qed.

Lemma direct_super_interface_trans : forall classes a b c cB,
  direct_super_interface classes a b ->
  CP.class_loaded  classes b cB ->
  C.class_interface cB = true ->
  direct_super_interface classes (C.class_interfaces cB) c ->
  direct_super_interface classes a c.
intros. induction H; eauto using d_inter_step_up, d_inter_step_along.
Qed.

Lemma assignable_refl : forall classes nmA cA,
  CP.class_loaded  classes nmA cA ->
  assignable classes (C.ty_obj nmA) (C.ty_obj nmA).
intros classes nmA cA cA_exists.
destruct (bool_dec (C.class_interface cA)) as [A_interface | A_class].
 (* A is an interface *)
 eapply assign_interface_interface_refl; eauto.
 (* A is a class *)
 eapply assign_class_class; eauto. eapply sub_class_refl. eauto.
Qed.

Lemma assignable_trans : forall classes a b c,
  assignable classes a b ->
  assignable classes b c ->
  assignable classes a c.
intros. induction H.
 (* assign_class_class a b *)
 set (b:=C.ty_obj nmT) in H0. set (e:=refl_equal b : b = C.ty_obj nmT).
 generalize b e H0. clear b e H0. intros.
 induction H0; inversion e; subst; try clu_congruence.
  (* assign_class_class b c *)
  eapply assign_class_class; eauto. eapply sub_class_trans; eauto.
  (* assign_class_interface b c *)
  eapply assign_class_interface. 
   apply H.
   apply H5.
   apply H6.
   apply H2.
   apply H8.
   apply H9.
   eapply sub_class_trans; eauto.
   apply H11.
 (* assign_class_interface a b *)
 set (b:=C.ty_obj nmT) in H0. set (e:=refl_equal b : b = C.ty_obj nmT).
 generalize b e H0. clear b e H0. intros.
 induction H0; inversion e; subst; try clu_congruence.
  (* assign_interface_class b c *)
  eapply assignable_Object. apply H.
  (* assign_interface_interface_refl b c *)
  eapply assign_class_interface.
   apply H. apply H0. apply H2. assumption. assumption. assumption. assumption. assumption.
  (* assign_interface_interface_strict b c *)
  eapply assign_class_interface.
   apply H. apply H8. apply H2. assumption. assumption. assumption. assumption.
   eapply direct_super_interface_trans; eassumption.
 (* assign_interface_object *)
 rewrite (assignable_Object_only _ _ H0). eapply assignable_Object. apply H.
 (* assign_interface_interface_refl *)
 assumption.
 (* assign_interface_interface_strict *)
 set (b:=C.ty_obj nmT) in H0. set (e:=refl_equal b : b = C.ty_obj nmT).
 generalize b e H0. clear b e H0. intros.
 induction H0; inversion e; subst; try clu_congruence.
  (* assign_interface_class *)
  eapply assignable_Object. apply H.
  (* assign_interface_interface_refl *)
  eapply assign_interface_interface_strict; eauto.
  (* assign_interface_interface_strict *)
  rewrite (CP.class_loaded_unique H1 H0) in *. eapply assign_interface_interface_strict; eauto.
  eapply direct_super_interface_trans; eauto.
Qed.

(* Checking of assignability *)

Fixpoint check_subclass_aux (classes:CP.cert_classpool)
                            (next_name:option B.Classname.t)
                            (nm:B.Classname.t)
                            (scc:CP.super_class_chain classes next_name)
                            {struct scc}
                          : bool
 :=
 match option_informative next_name with
 | inleft (exist super_nm super_nm_eq) =>
    match B.Classname.eq_dec super_nm nm with
    | left _ => true
    | right _ =>
       let not_not_there := CP.super_class_chain_not_not_there super_nm_eq scc in
       match CP.class_loaded_dec classes super_nm with
       | inleft (exist super_c super_c_exists) =>
          check_subclass_aux classes (C.class_super_class super_c) nm (CP.super_class_chain_inv super_c_exists super_nm_eq scc)
       | inright not_there =>
          match not_not_there not_there with end
       end
    end
 | inright _ =>
    false
 end.

Definition check_subclass : forall classes c,
  CP.class_loaded  classes (C.class_name c) c ->
  B.Classname.t ->
  bool
 := fun classes c c_exists nm_t =>
 match B.Classname.eq_dec (C.class_name c) nm_t with
 | left _ => true
 | right _ =>
    match bool_informative (C.class_interface c) with
    | left is_interface =>
       if B.Classname.eq_dec nm_t B.java_lang_Object then true else false
    | right is_class =>
       let scc := CP.cert_classpool_gives_scc c_exists is_class in
       check_subclass_aux classes (C.class_super_class c) nm_t scc
    end
 end.
Implicit Arguments check_subclass [classes c].

Lemma check_subclass_aux_sound : forall classes nm_s nm_t scc,
  check_subclass_aux classes nm_s nm_t scc = true ->
  match nm_s with
  | None => False
  | Some nm_s => sub_class classes nm_s nm_t
  end.
intros classes c nm scc. elim scc using CP.super_class_chain_induction; intros; simpl in *.

discriminate.

destruct (B.Classname.eq_dec nm0 nm). 
 (* names are equal *)
 subst. eapply sub_class_refl. eauto.
 (* names not equal *)
 destruct (CP.class_loaded_dec classes nm0) as [[c' c'_loaded] | no_c'].
  (* the class was found *)
  pose (H _ _ H0).
  generalize y. clear y H0. intro H2.
  destruct (option_dec (C.class_super_class c')) as [[x0 update_res]|update_res]; rewrite update_res in H2.
   apply (sub_class_step classes nm0 nm x0 c'); assumption.
   contradiction.
  (* class not found *)
  elimtype False. apply no_c'. eauto. 
Qed. 

Lemma check_subclass_aux_complete : forall classes nm_s nm_t scc,
  sub_class classes nm_s nm_t ->
  check_subclass_aux classes (Some nm_s) nm_t scc = true.
intros. 
induction H. 
 destruct (CP.scc_Some _ _ scc) as [c [c_exists [c_class [s e]]]]. rewrite e.
 simpl. destruct (B.Classname.eq_dec nm nm).
  reflexivity.
  elimtype False. apply n. reflexivity.
 destruct (CP.scc_Some _ _ scc) as [c' [c'_exists [c'_class [s e]]]]. rewrite e.
 simpl. destruct (B.Classname.eq_dec nm nm_t).
  reflexivity. 
  destruct (CP.class_loaded_dec classes nm) as [[super_c super_c_exists] | no_super_c].
   assert (c = super_c) by eauto using CP.class_loaded_unique. subst.
   set (scc':=(s super_c (eq_ind_r (fun nm => CP.class_loaded  classes nm super_c) super_c_exists (refl_equal nm)))).
   generalize scc'. clear scc' s H super_c_exists H1. rewrite H0. apply IHsub_class. 
   elimtype False. apply no_super_c. exists c. assumption.
Qed.

Lemma check_subclass_sound : forall classes c nm_t c_exists,
  check_subclass (classes:=classes) (c:=c) c_exists nm_t = true -> sub_class classes (C.class_name c) nm_t.
intros. unfold check_subclass in H. 
destruct (B.Classname.eq_dec (C.class_name c) nm_t).
 (* names are equal *)
 subst. eapply sub_class_refl. apply c_exists.
 (* names not equal *)
 destruct (bool_informative (C.class_interface c)).
  (* is an interface: case not fully handled yet *)
  destruct (B.Classname.eq_dec nm_t B.java_lang_Object).
   subst. 
   destruct (CP.cert_classpool_has_Object classes). 
   eapply sub_class_step. 
    apply c_exists.
    apply (CP.cert_classpool_gives_interface_super_class_Object c_exists e).
    destruct H0. eapply sub_class_refl. apply H0.
   discriminate.
  (* is a class *)
  pose (check_subclass_aux_sound _ _ _ _ H).
  generalize y. clear y H. intro H. destruct (option_dec (C.class_super_class c)) as [[x update_res]|update_res]; rewrite update_res in H.
   eapply sub_class_step; eauto.
   contradiction.
Qed.

Lemma check_subclass_complete : forall classes c c_exists nm_t,
  sub_class classes (C.class_name c) nm_t -> check_subclass (classes:=classes) (c:=c) c_exists nm_t = true.
intros. unfold check_subclass.
destruct (B.Classname.eq_dec (C.class_name c) nm_t).
 reflexivity.
 inversion H.
  (* reflexivity *) 
  contradiction.
  (* step *)
  destruct (bool_informative (C.class_interface c)).
   (* is an interface *)
   rewrite (CP.class_loaded_unique H0 c_exists) in *. 
   rewrite (CP.cert_classpool_gives_interface_super_class_Object c_exists e) in H1.
   inversion H1. rewrite <- H4 in H2. inversion H2. 
    (* refl *)
    subst. subst. destruct (B.Classname.eq_dec B.java_lang_Object B.java_lang_Object).
     reflexivity.
     elimtype False. apply n0. reflexivity.
    (* step *)
    destruct (CP.cert_classpool_has_Object classes) as [object [object_exists [no_super _]]]. 
    subst. clu_congruence.
   (* not an interface *)
   set (scc':=CP.cert_classpool_gives_scc c_exists e).
   generalize scc'. clear scc'. 
   rewrite (CP.class_loaded_unique c_exists H0) in *. rewrite H1. 
   intro. apply check_subclass_aux_complete. assumption.  
Qed.

Fixpoint check_direct_super_interface (classes:CP.cert_classpool)
                                      (interface_list:list B.Classname.t)
                                      (nm:B.Classname.t)
                                      (gil:CP.good_interface_list2 classes interface_list)
                                      {struct gil}
                                    : bool
 :=
 match interface_list as il return (interface_list = il -> bool) with
 | nil => fun e : interface_list = nil =>
    false
 | i_nm::rest => fun e : interface_list = i_nm::rest =>
    match B.Classname.eq_dec i_nm nm with
    | left _ => true
    | right _ =>
       let gil_rest      := CP.good_interface_list2_inv_2 gil e in
       let not_not_there := CP.good_interface_list2_not_not_there gil e in
        match CP.class_loaded_dec classes i_nm with
        | inleft (exist i i_exists) =>
           let g_supers := CP.good_interface_list2_inv_1 gil e i_exists in
            if check_direct_super_interface classes (C.class_interfaces i) nm g_supers then
              true
            else
              check_direct_super_interface classes rest nm gil_rest
        | inright not_there =>
           match not_not_there not_there with end
        end
    end
 end (refl_equal interface_list).

Lemma check_direct_super_interface_sound : forall classes i_list nmT gil,
  check_direct_super_interface classes i_list nmT gil = true ->
  direct_super_interface classes i_list nmT.
intros classes i_list nmT gil.
elim gil using CP.good_interface_list2_induction; intros; simpl in *.
 (* empty list *)
 discriminate.
 (* otherwise... *)
 destruct (B.Classname.eq_dec i_nm nmT).
  (* found it! *)
  subst. apply d_inter_here.
  (* otherise, plodding on... *)
  destruct (CP.class_loaded_dec classes0 i_nm) as [[c' c'_exists] | no_c'].
   (* found the interface *)
   match goal with H:match ?x with true => true | false => _ end = true |- _ => destruct (bool_dec x) end.
    assert (C.class_interface c' = true). clear H1 H2. rewrite (CP.class_loaded_unique c'_exists c). assumption.
    eapply d_inter_step_up; eauto.
    rewrite H2 in H1. eapply d_inter_step_along; eauto.
   (* interface not found: unpossible! *)
   elimtype False. apply no_c'. eauto.  
Qed.

Lemma check_direct_super_interface_complete : forall classes i_list nmT gil,
  direct_super_interface classes i_list nmT ->
  check_direct_super_interface classes i_list nmT gil = true.
intros. induction H.
 (* refl case *)
 destruct (CP.gil2_inv_cons gil) as [i [i_exists [i_interface [go_up [go_along eq]]]]].
 rewrite eq. simpl. destruct (B.Classname.eq_dec nmT nmT).
  reflexivity.
  elimtype False. apply n. reflexivity.
 (* up case *)
 destruct (CP.gil2_inv_cons gil) as [i [i_exists [i_interface [go_up [go_along eq]]]]]. rewrite eq.
 simpl. destruct (B.Classname.eq_dec nmX nmT).
  (* names equal *)
  reflexivity.
  (* names unequal *)
  destruct (CP.class_loaded_dec classes nmX) as [[c c_exists] | no_c].
   (* class found *)
   rewrite (CP.class_loaded_unique H c_exists) in IHdirect_super_interface. rewrite IHdirect_super_interface. reflexivity.
   (* class not found *)
   elimtype False. apply no_c. eauto.
 (* along case *)
 destruct (CP.gil2_inv_cons gil) as [i [i_exists [i_interface [go_up [go_along eq]]]]]. rewrite eq.
 simpl. destruct (B.Classname.eq_dec nmX nmT).
  (* names equal *)
  reflexivity.
  (* names unequal *)
  destruct (CP.class_loaded_dec classes nmX) as [[c c_exists] | no_c].
   (* class found *)
   match goal with |- match ?x with true => true | false => _ end = true => destruct x end.
    reflexivity.
    auto.
   (* class not found *)
   elimtype False. apply no_c. eauto. 
Qed.

Fixpoint check_class_implements_aux (classes:CP.cert_classpool)
                                    (next_name:option B.Classname.t)
                                    (nmT:B.Classname.t)
                                    (scc:CP.super_class_chain classes next_name)
                                    {struct scc}
                                  : bool
 :=
 match option_informative next_name with
 | inleft (exist super_nm super_nm_eq) =>
    let not_not_there := CP.super_class_chain_not_not_there super_nm_eq scc in
    match CP.class_loaded_dec classes super_nm with
    | inleft (exist super_c super_c_exists) =>
       let gil := CP.cert_classpool_gives_gil2 super_c_exists in
         if check_direct_super_interface classes (C.class_interfaces super_c) nmT gil then
           true
         else
           check_class_implements_aux classes (C.class_super_class super_c) nmT (CP.super_class_chain_inv super_c_exists super_nm_eq scc)
    | inright not_there =>
       match not_not_there not_there with end
    end
 | inright _ =>
    false
 end.

Definition check_class_implements : forall classes c,
  CP.class_loaded  classes (C.class_name c) c ->
  C.class_interface c = false ->
  B.Classname.t ->
  bool
 := fun classes c c_exists is_class nmT =>
 let gil := CP.cert_classpool_gives_gil2 c_exists in
  if check_direct_super_interface classes (C.class_interfaces c) nmT gil then
    true
  else
    let scc := CP.cert_classpool_gives_scc c_exists is_class in
    check_class_implements_aux classes (C.class_super_class c) nmT scc.

Lemma check_class_implements_aux_sound : forall classes opt_nmS nmT scc,
  check_class_implements_aux classes opt_nmS nmT scc = true ->
  match opt_nmS with
  | None => False
  | Some nmS => exists nmS', exists cS',
                  CP.class_loaded  classes nmS' cS' /\
                  C.class_interface cS' = false /\
                  sub_class classes nmS nmS' /\
                  direct_super_interface classes (C.class_interfaces cS') nmT
  end.
intros classes opt_nmS nmT scc. elim scc using CP.super_class_chain_induction; intros; simpl in *.
 (* no super class *)
 discriminate.
 (* some super class *)
 destruct (CP.class_loaded_dec classes nm) as [[cl cl_exists] | no_cl].
  (* class exists *)
  match goal with _:match ?x with true => true | false => _ end = true |- _ => destruct (bool_dec x) end.
   (* this class implements the interface *)
   rewrite (CP.class_loaded_unique e cl_exists) in *.
   exists nm. exists cl. intuition.
    eapply sub_class_refl. eauto.
    eapply check_direct_super_interface_sound. eassumption.
   (* this class doesn't directly implement the interface *)
   rewrite H1 in H0.
   pose (H _ _ H0). generalize y. clear y H0. intro. 
   destruct (option_dec (C.class_super_class cl)) as [[nm' nm'_eq] | no_nm'].
    rewrite nm'_eq in y. destruct y as [nmS' [cS' [nmS'_cS' [cS'_not_interface [nm'_sub_nmS' dsi]]]]].
    exists nmS'. exists cS'. intuition. eapply sub_class_step; eassumption.
    rewrite no_nm' in y. contradiction.
  (* class does not exist *)
  elimtype False. apply no_cl. eauto.
Qed.

Lemma check_class_implements_aux_complete : forall classes nmS nmT scc,
  (exists nmS', exists cS',
    CP.class_loaded  classes nmS' cS' /\
    C.class_interface cS' = false /\
    sub_class classes nmS nmS' /\
    direct_super_interface classes (C.class_interfaces cS') nmT) ->
  check_class_implements_aux classes (Some nmS) nmT scc = true.
intros classes nmS nmT scc [nmS' [cS' [S'_loaded [S'_not_interface [S_sub_S' S'_sub_T]]]]].
induction S_sub_S'.
 (* direct implementation *)
 destruct (CP.scc_Some _ _ scc) as [c [c_exists [s [s2 eq]]]]. rewrite eq.
 simpl. destruct (CP.class_loaded_dec classes nm) as [[super_c super_c_exists] | no_super].
  (* class exists *)
  rewrite (CP.class_loaded_unique S'_loaded super_c_exists) in *. 
  rewrite (check_direct_super_interface_complete _ _ _ (CP.cert_classpool_gives_gil2 super_c_exists) S'_sub_T).
  reflexivity.
  (* no class: unpossible! *)
  elimtype False. apply no_super. eauto.
 (* super has an implementation *)
 destruct (CP.scc_Some _ _ scc) as [c' [c'_exists [s [s2 eq]]]]. rewrite eq.
 simpl. destruct (CP.class_loaded_dec classes nm) as [[super_c super_c_exists] | no_super].
  (* class exists *)
  match goal with |- match ?x with true => true | false => _ end = true => destruct x end.
   (* this class actually directly implemented it *)
   reflexivity.
   (* need to step on *)
   rewrite (CP.class_loaded_unique H super_c_exists) in *.
   match goal with |- (check_class_implements_aux _ _ _ ?x) = true => set (scc':=x) end.
   generalize scc'. clear scc'. rewrite H0. intro. apply IHS_sub_S'. apply S'_loaded. 
  (* no class: unpossible, again *)
  elimtype False. apply no_super. eauto.
Qed.

Lemma check_class_implements_sound : forall classes c c_exists c_class nmT,
  check_class_implements classes c c_exists c_class nmT = true ->
  exists nmS', exists cS',
    CP.class_loaded  classes nmS' cS' /\
    C.class_interface cS' = false /\
    sub_class classes (C.class_name c) nmS' /\
    direct_super_interface classes (C.class_interfaces cS') nmT.
intros. unfold check_class_implements in H.
match goal with _:match ?x with true => _ | false => _ end = true |- _ => destruct (bool_dec x) end.
 rewrite H0 in H. exists (C.class_name c). exists c. intuition.
  eapply sub_class_refl. eauto.
  eapply check_direct_super_interface_sound. apply H0.
 rewrite H0 in H.
 set (B:=check_class_implements_aux_sound _ _ _ _ H).
 destruct (option_dec (C.class_super_class c)) as [[nm' nm'_eq] | no_nm'].
  rewrite nm'_eq in B. destruct B as [nmS' [cS' [S'_loaded [S'_not_interface [nm'_S' S'_T]]]]].
   exists nmS'. exists cS'. intuition. eapply sub_class_step; eassumption. 
  rewrite no_nm' in B. contradiction.
Qed.

Lemma check_class_implements_complete : forall classes c c_exists c_class nmT,
  (exists nmS', exists cS',
    CP.class_loaded  classes nmS' cS' /\
    C.class_interface cS' = false /\
    sub_class classes (C.class_name c) nmS' /\
    direct_super_interface classes (C.class_interfaces cS') nmT) ->
  check_class_implements classes c c_exists c_class nmT = true.
intros. unfold check_class_implements. destruct H as [nmS' [cS' [S'_loaded [S'_not_interface [c_S' S'_T]]]]].
inversion c_S'; subst.
 (* direct implementation *)
 rewrite (CP.class_loaded_unique S'_loaded c_exists) in S'_T.
 rewrite (check_direct_super_interface_complete _ _ _ (CP.cert_classpool_gives_gil2 c_exists) S'_T).
 reflexivity.
 (* super implementation *)
 match goal with |- match ?x with true => _ | false => _ end = true => destruct x end.
  (* there was actually a direct implementation *)
  reflexivity.
  (* continue up the hierarchy *)
  set (scc:=CP.cert_classpool_gives_scc c_exists c_class).
  generalize scc. clear scc. rewrite (CP.class_loaded_unique H c_exists) in *. 
  rewrite H0.
  intro. apply check_class_implements_aux_complete.
  intuition eauto 6.
Qed.

Definition check_assignable : CP.cert_classpool -> C.java_ref_type -> C.java_ref_type -> bool :=
  fun classes S T =>
  match S with
  | C.ty_obj nmS =>
     match T with
     | C.ty_obj nmT =>
        match CP.class_loaded_dec classes nmS with
        | inleft (exist cS cS_exists) =>
           match CP.class_loaded_dec classes nmT with
           | inleft (exist cT cT_exists) =>
              match bool_informative (C.class_interface cS) with
              | left S_is_interface =>
                 match bool_informative (C.class_interface cT) with
                 | left T_is_interface =>
                    match B.Classname.eq_dec nmS nmT with
                    | left _ =>
                       true
                    | right _ =>
                       let gil := CP.cert_classpool_gives_gil2 cS_exists in
                        check_direct_super_interface classes (C.class_interfaces cS) nmT gil
                    end
                 | right _ =>
                    match B.Classname.eq_dec nmT B.java_lang_Object with
                    | left _ => true
                    | right _ => false
                    end
                 end
              | right S_is_class =>
                 let cS_exists := CP.cert_classpool_names cS_exists in
                 match bool_informative (C.class_interface cT) with
                 | left T_is_interface =>
                    check_class_implements classes cS cS_exists S_is_class nmT
                 | right T_is_class =>
                    check_subclass cS_exists nmT
                 end
              end
           | inright _ =>
              false
           end
        | inright _ =>
           false
        end
     | C.ty_arr _ =>
        false
     end
  | C.ty_arr _ =>
     false
  end.

Lemma check_assignable_sound : forall classes S T,
  check_assignable classes S T = true ->
  assignable classes S T.
unfold check_assignable. intros.
destruct S as [nmS|]; try discriminate.
destruct T as [nmT|]; try discriminate.
destruct (CP.class_loaded_dec classes nmS) as [[cS cS_exists] | no_cS].
 (* S exists *)
 destruct (CP.class_loaded_dec classes nmT) as [[cT cT_exists] | no_cT].
  (* T exists *)
  destruct (bool_informative (C.class_interface cS)) as [S_is_interface | S_is_class].
   (* S is an interface *)
   destruct (bool_informative (C.class_interface cT)) as [T_is_interface | T_is_class].
    (* T is an interface *)
    destruct (B.Classname.eq_dec nmS nmT) as [S_eq_T | S_neq_T].
     (* they are equal *)
     subst. eapply assign_interface_interface_refl; eauto.
     (* not equal *)
     eapply assign_interface_interface_strict; eauto.
     eapply check_direct_super_interface_sound. apply H.
    (* T is a class *)
    destruct (B.Classname.eq_dec nmT B.java_lang_Object) as [T_is_Object | T_notObject].
     (* T is j.l.Object *)
     subst. eapply assign_interface_class; eauto.
     (* T not Object *)
     discriminate.
   (* S is a class *)
   destruct (bool_informative (C.class_interface cT)) as [T_is_interface | T_is_class].
    (* T is an interface *)
    destruct (check_class_implements_sound _ _ _ _ _ H) as [nmS' [cS' [S'_loaded [S'_not_interface [S_S' S'_T]]]]].
    eapply assign_class_interface; eauto.
    rewrite <- (CP.cert_classpool_names_2 cS_exists). assumption. 
    (* T is a class *)
    eapply assign_class_class; eauto.
    rewrite <- (CP.cert_classpool_names_2 cS_exists). 
    eapply check_subclass_sound. apply H.
  (* T doesn't exist *)
  discriminate.
 (* S doesn't exist *)
 discriminate.
Qed.

Lemma check_assignable_complete : forall classes S T,
  assignable classes S T ->
  check_assignable classes S T = true.
intros. unfold check_assignable.
destruct H.
 (* assign_class_class *)
 destruct (CP.class_loaded_dec classes nmS) as [[cS0 cS_exists] | no_cS].
  (* S exists *)
  rewrite (CP.class_loaded_unique H cS_exists) in * |- *.
  destruct (CP.class_loaded_dec classes nmT) as [[cT0 cT_exists] | no_cT].
   (* T exists *)
   rewrite (CP.class_loaded_unique H0 cT_exists) in * |- *.
   destruct (bool_informative (C.class_interface cS0)) as [cS_is_interface | cS_is_class].
    (* S interface: impossible *)
    congruence.
    (* S class *)
    destruct (bool_informative (C.class_interface cT0)) as [cT_interface | cT_class].
     (* T interface *)
     congruence.
     (* T class *)
     apply check_subclass_complete. rewrite (CP.cert_classpool_names_2 cS_exists). assumption.
   (* no T: impossible *)
   elimtype False. apply no_cT. eauto.
  (* no S: impossible *)
  elimtype False. apply no_cS. eauto.
 (* assign_class_interface *)
 destruct (CP.class_loaded_dec classes nmS) as [[cS0 cS_exists] | no_cS].
  (* S exists *)
  rewrite (CP.class_loaded_unique H cS_exists) in * |- *. clear H cS.
  destruct (CP.class_loaded_dec classes nmT) as [[cT0 cT_exists] | no_cT].
   (* T exists *)
  rewrite (CP.class_loaded_unique H0 cT_exists) in * |- *. clear H0 cT.
   destruct (bool_informative (C.class_interface cS0)) as [cS_is_interface | cS_is_class].
    (* S interface: impossible *)
    congruence.
    (* S class *)
    destruct (bool_informative (C.class_interface cT0)) as [cT_interface | cT_class].
     (* T interface *)
     apply check_class_implements_complete. rewrite (CP.cert_classpool_names_2 cS_exists). intuition eauto 6.
     (* T class: impossible *)
     congruence.
   (* no T: impossible *)
   elimtype False. apply no_cT. eauto.
  (* no S: impossible *)
  elimtype False. apply no_cS. eauto.
 (* assign_interface_class *)
 destruct (CP.cert_classpool_has_Object classes) as [object [object_exists [_ [_ object_class]]]].
 destruct (CP.class_loaded_dec classes nmS) as [[cS0 cS_exists] | no_cS].
  (* S exists *)
  rewrite (CP.class_loaded_unique H cS_exists) in * |- *. clear H cS.
  destruct (CP.class_loaded_dec classes B.java_lang_Object) as [[cT cT_exists] | no_cT].
   (* T exists *)
   rewrite (CP.class_loaded_unique object_exists cT_exists) in * |- *. clear object_exists object.
   destruct (bool_informative (C.class_interface cS0)) as [cS_interface | cS_class].
    (* S interface *)
    destruct (bool_informative (C.class_interface cT)) as [cT_interface | cT_class].
     (* T interface: impossible *)
     rewrite cT_interface in object_class. discriminate.
     (* T class *)
     destruct (B.Classname.eq_dec B.java_lang_Object B.java_lang_Object) as [is_eq | not_eq].
      (* of course... *)
      reflexivity.
      (* not *)
      elimtype False. apply not_eq. reflexivity.
    (* S class *)
    rewrite cS_class in H0. discriminate.
   (* no T: impossible *)
   elimtype False. apply no_cT. eauto.
  (* no S : impossible *)
  elimtype False. apply no_cS. eauto.
 (* assign_interface_interface_refl *)
 destruct (CP.class_loaded_dec classes nmS) as [[cS0 cS_exists] | no_cS].
  (* S exists *)
  rewrite (CP.class_loaded_unique H cS_exists) in * |- *. clear H cS.
  destruct (bool_informative (C.class_interface cS0)) as [S_interface | cS_class].
   (* S interface *)
   destruct (B.Classname.eq_dec nmS nmS) as [is_eq | not_eq].
    (* of course... *)
    reflexivity.
    (* not *)
    elimtype False. apply not_eq. reflexivity.
   (* S class *)
   rewrite cS_class in H0. discriminate.
  (* no S: impossible *)
  elimtype False. apply no_cS. eauto.
 (* assign_interface_interface_strict *)
 destruct (CP.class_loaded_dec classes nmS) as [[cS0 cS_exists] | no_cS].
  (* S exists *)
  rewrite (CP.class_loaded_unique H cS_exists) in * |- *. clear H cS.
  destruct (CP.class_loaded_dec classes nmT) as [[cT0 cT_exists] | no_cT].
   (* T exists *)
   rewrite (CP.class_loaded_unique H0 cT_exists) in * |- *. clear H0 cT.
   destruct (bool_informative (C.class_interface cS0)) as [cS_interface | cS_class].
    (* S interface *)
    destruct (bool_informative (C.class_interface cT0)) as [cT_interface | cT_class].
     (* T interface *)
     destruct (B.Classname.eq_dec nmS nmT) as [S_eq_T | S_neq_T].
      (* are equal *)
      reflexivity.
      (* not equal *)
      apply check_direct_super_interface_complete. apply H3.
     (* T class: impossible *)
     rewrite cT_class in H2. discriminate.
    (* S class: impossible *)
    rewrite cS_class in H1. discriminate.
   (* no T: impossible *)
   elimtype False. apply no_cT. eauto.
  (* no S: impossible *)
  elimtype False. apply no_cS. eauto.
Qed.

Definition is_assignable : forall classes S T, {assignable classes S T}+{~assignable classes S T}.
intros classes S T.
destruct (bool_informative (check_assignable classes S T)) as [is_true | is_false].
 left. apply check_assignable_sound. apply is_true.
 right. unfold not. intro. rewrite (check_assignable_complete _ _ _ H) in is_false. discriminate.
Defined. 

(* preservation of assignability *)

Lemma preserve_subclass : forall classesA classesB nm_s nm_t,
  sub_class classesA nm_s nm_t ->
  CP.preserve_old_classes classesA classesB ->
  sub_class classesB nm_s nm_t.
intros. unfold CP.preserve_old_classes in *. induction H. 
 eapply sub_class_refl; eauto.
 eapply sub_class_step; eauto.
Qed.
Hint Resolve preserve_subclass.

Lemma preserve_subclass_rev : forall classesA classesB nm_s c_s nm_t,
  CP.class_loaded classesA nm_s c_s ->
  sub_class classesB nm_s nm_t ->
  CP.preserve_old_classes classesA classesB ->
  sub_class classesA nm_s nm_t.
Proof.
  intros until nm_t. intros loaded_s subclass preserve.
  generalize c_s loaded_s.
  clear c_s loaded_s.
  induction subclass; intros.
    eapply sub_class_refl; eauto.

    pose (loaded_s' := preserve nm c_s loaded_s).
    clearbody loaded_s'.
    rewrite (CP.class_loaded_unique H loaded_s') in H0.
    eapply sub_class_step; eauto.
    destruct (CP.class_super_loaded _ _ _ _ loaded_s H0).
    eapply IHsubclass; eauto.
Qed.

Lemma preserve_direct_super_interface : forall classesA classesB nm_s nm_t,
  direct_super_interface classesA nm_s nm_t ->
  CP.preserve_old_classes classesA classesB ->
  direct_super_interface classesB nm_s nm_t.
intros classesA classesB nm_s nm_t direct1 preserve1.
unfold CP.preserve_old_classes in preserve1.
induction direct1; eauto using d_inter_here, d_inter_step_up, d_inter_step_along.
Qed.
Hint Resolve preserve_direct_super_interface.

Lemma preserve_assignable : forall classesA classesB S T,
  assignable classesA S T ->
  CP.preserve_old_classes classesA classesB ->
  assignable classesB S T.
intros classesA classesB S T assignable1 preserve1.
unfold CP.preserve_old_classes in preserve1. unfold assignable in *.
destruct assignable1; eauto 7 using assign_class_class, assign_class_interface, assign_interface_class, assign_interface_interface_refl, assign_interface_interface_strict.
Qed.

Lemma superclass_loaded : forall classes nm_s c_s nm_t,
  CP.class_loaded classes nm_s c_s ->
  sub_class classes nm_s nm_t ->
  exists c, CP.class_loaded classes nm_t c.
Proof.
  intros.
  generalize nm_s c_s H.
  clear H.
  induction H0; intros.
    exists cwitness.  assumption.
    eapply IHsub_class; eauto.
Qed.

Lemma interfaces_loaded : forall classes nmA cA nmB,
  CP.class_loaded classes nmA cA ->
  In nmB (C.class_interfaces cA) ->
  exists cB, CP.class_loaded classes nmB cB.
Proof.
  intros classes nmA cA nmB loadedA in_ifaces.
  pose (good := CP.cert_classpool_gives_gil2 loadedA).
  clearbody good.
  set (ifaces := C.class_interfaces cA) in *.
  induction good.
    inversion in_ifaces.

    inversion in_ifaces.
      subst i_nm. exists i. assumption.

      apply IHgood; auto.
Qed.

Lemma super_interface_loaded : forall classes nmA cA nmB,
  CP.class_loaded classes nmA cA ->
  direct_super_interface classes (C.class_interfaces cA) nmB ->
  exists cB, CP.class_loaded classes nmB cB.
Proof.
  intros classes nmA cA nmB loadedA supers.
  set (ifaces := C.class_interfaces cA) in *.
  assert (in_ifaces : forall iface, In iface ifaces -> In iface (C.class_interfaces cA)) by auto.
  clearbody ifaces.
  generalize nmA cA loadedA in_ifaces.
  clear nmA cA loadedA in_ifaces.
  induction supers; intros.
    eapply interfaces_loaded; eauto. apply in_ifaces. left. reflexivity.

    apply IHsupers with (nmA:=nmX) (cA:=cX); auto.

    apply IHsupers with (nmA:=nmA) (cA:=cA); auto.
    intros. apply in_ifaces. right. assumption.
Qed.

Lemma assignable_loaded : forall classes nmA cA nmB,
  CP.class_loaded classes nmA cA ->
  assignable classes (C.ty_obj nmA) (C.ty_obj nmB) ->
  exists cB, CP.class_loaded classes nmB cB.
Proof.
  intros.
  inversion H0; eauto.
  destruct (CP.cert_classpool_has_Object classes) as [obj [loaded _]].
  eauto.
Qed.

Lemma preserve_superinterfaces_rev : forall classesA classesB nmA cA nmB,
  CP.class_loaded classesA nmA cA ->
  CP.preserve_old_classes classesA classesB ->
  direct_super_interface classesB (C.class_interfaces cA) nmB ->
  direct_super_interface classesA (C.class_interfaces cA) nmB.
Proof.
  intros.
  set (ifaces := C.class_interfaces cA) in *.
  assert (in_ifaces : forall iface, In iface ifaces -> In iface (C.class_interfaces cA)) by auto.
  clearbody ifaces.
  generalize nmA cA H in_ifaces.
  clear nmA cA H in_ifaces.
  induction H1; eauto using d_inter_here, d_inter_step_up, d_inter_step_along.
    intros.
    destruct (interfaces_loaded classesA nmA cA nmX); eauto.  apply in_ifaces. left. reflexivity.
    rewrite (CP.class_loaded_unique (H0 _ _ H4) H) in H4.
    apply d_inter_step_up with (cX:=cX); auto.
    apply IHdirect_super_interface with (nmA:=nmX) (cA:=cX); auto.

    intros.
    apply d_inter_step_along.
    apply IHdirect_super_interface with (nmA:=nmA) (cA:=cA); auto.
    intros. apply in_ifaces. right. assumption.
Qed.

Lemma preserve_assignable_rev : forall classesA classesB nmA cA nmB,
  assignable classesB (C.ty_obj nmA) (C.ty_obj nmB) ->
  CP.class_loaded classesA nmA cA ->
  C.class_interface cA = false ->
  CP.preserve_old_classes classesA classesB ->
  assignable classesA (C.ty_obj nmA) (C.ty_obj nmB).
Proof.
  intros until nmB; intros assign loaded_A notint_A preserve.
  inversion assign; subst.
    apply preserve_subclass_rev with (classesA:=classesA) (c_s:=cA) in H5; auto.
    eapply assign_class_class; eauto.
    destruct (superclass_loaded classesA nmA cA nmB); eauto.
    rewrite (CP.class_loaded_unique H2 (preserve _ _ H)). assumption.

    rewrite (CP.class_loaded_unique H1 (preserve _ _ loaded_A)) in *.
    apply preserve_subclass_rev with (classesA:=classesA) (c_s:=cA) in H7; auto.
    destruct (superclass_loaded classesA nmA cA nmS'); eauto.
    rewrite (CP.class_loaded_unique (preserve _ _ H) H3) in H.
    apply (preserve_superinterfaces_rev classesA classesB nmS' cS' nmB) in H8; auto.
    destruct (super_interface_loaded classesA nmS' cS' nmB) as [cT' loadedB']; auto.
    rewrite (CP.class_loaded_unique (preserve _ _ loadedB') H2) in loadedB'.
    eapply (assign_class_interface classesA nmA nmB cA cT nmS' cS'); eauto.

    rewrite (CP.class_loaded_unique H1 (preserve _ _ loaded_A)) in *.
    eapply assign_interface_class; eauto.

    rewrite (CP.class_loaded_unique H1 (preserve _ _ loaded_A)) in *.
    eapply assign_interface_interface_refl; eauto.

    rewrite (CP.class_loaded_unique H1 (preserve _ _ loaded_A)) in *.
    apply (preserve_superinterfaces_rev classesA classesB nmA cA nmB) in H5; auto.
    destruct (super_interface_loaded classesA nmA cA nmB) as [cT' loadedB']; auto.
    rewrite (CP.class_loaded_unique (preserve _ _ loadedB') H2) in loadedB'.
    eapply assign_interface_interface_strict; eauto.
Qed.

Lemma subclass_distinct : forall classes nm c nm' nm_t,
  CP.class_loaded classes nm c ->
  C.class_super_class c = Some nm' ->
  C.class_interface c = false ->
  sub_class classes nm' nm_t ->
  nm <> nm_t.
Proof.
  intros.
  intro nmeq.
  subst nm_t.
  set (scc:=CP.cert_classpool_gives_scc H H1).
  clearbody scc.
  set (x:=C.class_super_class c).
  assert (xeq :C.class_super_class c = x) by reflexivity.
  rewrite xeq in scc.
  generalize x scc nm c nm' H H0 H1 H2 xeq.
  clear - classes.
  induction 1 using CP.super_class_chain_induction.
    intros.
    rewrite H0 in xeq.
    discriminate.

    intros.
    rewrite xeq in H1.
    injection H1 as nmeq'.
    subst nm'.
    destruct H3.
      rewrite (CP.class_loaded_unique e H0) in *.
      clear H3.
      eapply (H c0 H0); eauto.
      eapply sub_class_refl; eauto.

      eapply H; eauto.
      apply CP.class_super_interface with (classes:=classes) (nm1:=nm_t) (nm2:=nm) (c1:=c0) (c2:=c1); auto.
      eapply sub_class_trans. apply H5. eapply sub_class_step; eauto. eapply sub_class_refl; eauto.
Qed.

End MkAssignability.
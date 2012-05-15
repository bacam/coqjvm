Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import ClasspoolIface.
Require Import Execution.
Require Import Verifier.
Require Import Arith.
Require Import Omega.
Require Import List.
Require Import ListExt.
Require Import Store.
Require Import Peano_dec.
Require Import OptionExt.
Require Import OptionMonad.
Require Import DestructExt.

Module PreVerifierSafety (B0 : BASICS).

Module B := B0.

Module PreV := Verifier.MkPreVerifier B.

Module MkVerifierSafety (C : CLASSDATATYPES with Module B := B with Module A := PreV.VA)
                        (R  : CLASSPOOL with Module B := B with Module C := C).

Module E := Execution.Execution B C R.
Module V := PreV.MkVerifier C.

Section Satisfiability.

Hypothesis classes : R.cert_classpool.
Hypothesis heap : E.ObjectHeap.t.

Inductive rt_ty_sat : E.rt_val -> PreV.VA.value_assertion -> Prop :=
| ty_sat_int    : forall i, rt_ty_sat (E.rt_int i) C.A.va_int
| ty_sat_float  : rt_ty_sat E.rt_float C.A.va_float
| ty_sat_null   : rt_ty_sat (E.rt_addr None) C.A.va_null
| ty_sat_addr1  : forall x, rt_ty_sat (E.rt_addr None) (C.A.va_addr x)
| ty_sat_addr2  : forall nm a nm' fields,
    E.ObjectHeap.lookup heap a = Some (E.hp_object nm' fields) ->
    R.sub_class classes nm' nm ->
    rt_ty_sat (E.rt_addr (Some a)) (C.A.va_addr nm)
| ty_sat_ref_Some: forall a nm fields,
    E.ObjectHeap.lookup heap a = Some (E.hp_object nm fields) ->
    rt_ty_sat (E.rt_addr (Some a)) C.A.va_ref
| ty_sat_ref_None: rt_ty_sat (E.rt_addr None) C.A.va_ref
| ty_sat_cat1i  : forall i, rt_ty_sat (E.rt_int i) C.A.va_cat1
| ty_sat_cat1f  : rt_ty_sat E.rt_float C.A.va_cat1
| ty_sat_cat1a  : forall a, rt_ty_sat (E.rt_addr a) C.A.va_cat1
| ty_sat_double : rt_ty_sat E.rt_double C.A.va_double
| ty_sat_long   : rt_ty_sat E.rt_long C.A.va_long
| ty_sat_cat2d  : rt_ty_sat E.rt_double C.A.va_cat2
| ty_sat_cat2l  : rt_ty_sat E.rt_long C.A.va_cat2
| ty_sat_top    : forall v, rt_ty_sat v C.A.va_top.

Hint Resolve ty_sat_int ty_sat_float ty_sat_null ty_sat_addr1 ty_sat_addr2 ty_sat_ref_Some ty_sat_ref_None ty_sat_cat1i ty_sat_cat1f ty_sat_cat1a
             ty_sat_double ty_sat_long ty_sat_cat2d ty_sat_cat2l ty_sat_top.

Inductive stack_sat : list E.rt_val -> C.A.stack_assertion -> Prop :=
| stk_sat_nil  : forall l, stack_sat l nil
| stk_sat_cons : forall v t s a, rt_ty_sat v t -> stack_sat s a -> stack_sat (v::s) (t::a).

Inductive stack_sat_exact : list E.rt_val -> C.A.stack_assertion -> Prop :=
| stk_sat_exact_nil  : stack_sat_exact nil nil
| stk_sat_exact_cons : forall v t s a, rt_ty_sat v t -> stack_sat_exact s a -> stack_sat_exact (v::s) (t::a).

Inductive lvar_sat : list (option E.rt_val) -> C.A.lvar_assertion -> Prop :=
| lvar_sat_nil   : lvar_sat nil nil
| lvar_sat_cons1 : forall v t s a, rt_ty_sat v t -> lvar_sat s a -> lvar_sat (Some v::s) (t::a)
| lvar_sat_cons2 : forall s a, lvar_sat s a -> lvar_sat (None::s) (C.A.va_top::a).

Hypothesis class : C.class.

Definition subclass_assertions_satisfied :=
  forall a b, C.A.CP.S.lookup (C.A.class_annot_expected_subtypes (C.class_annotation class)) a = Some b ->
              R.sub_class classes a b.

Hypothesis all_expectations_met : subclass_assertions_satisfied.
  

Lemma leq_sub_class : forall a b,
  PreV.VA.CP.leq_prop (C.A.class_annot_expected_subtypes (C.class_annotation class)) a b ->
  R.sub_class classes a b.
intros. eapply PreV.VA.CP.leq_prop_LEQ.
 exact (R.sub_class_trans classes).
 intro. apply R.sub_class_refl.
 unfold PreV.VA.CP.all_LEQ. apply all_expectations_met. 
 assumption.
Save.

Lemma value_assertion_implication_sound : forall t1 t2 v,
  V.value_assertion_implication class t1 t2 -> rt_ty_sat v t1 -> rt_ty_sat v t2.
intros. induction H; destruct v; inversion H0; eauto.
 apply ty_sat_addr1.
 apply ty_sat_addr1.
 eapply ty_sat_addr2. 
  apply H3.
  eapply R.sub_class_trans. 
   apply H4. 
   apply leq_sub_class. apply H.
 subst o. auto. 
 subst o. auto.
 subst o. auto.
 subst o. auto.
 subst o. auto.
Save.

Hint Resolve value_assertion_implication_sound.

Lemma stack_assertion_implication_sound : forall a a' s,
  V.stack_assertion_implication class a a' -> stack_sat s a -> stack_sat s a'.
intros. generalize s H0. clear s H0. induction H; intros.
 apply stk_sat_nil.
 inversion H1. constructor; eauto.
Save.
 
Lemma lvar_assertion_implication_sound : forall a a' l,
  V.lvar_assertion_implication class a a' -> lvar_sat l a -> lvar_sat l a'.
intros. generalize l H0. clear l H0. induction H; intros.
inversion H0. apply lvar_sat_nil. 
inversion H1. 
 constructor; eauto.
 subst. inversion H; subst; try constructor; eauto. 
  rewrite (V.value_assertion_implication_top class t2 H). 
   apply lvar_sat_cons2. auto. 
Save.

Lemma sem_unpop : forall s a a' b b' ty,
  stack_sat s a ->
  V.unpop ty (b',a') = Some (b,a) ->
    b=b' /\ exists v, exists s', rt_ty_sat v ty /\ s = v::s' /\ stack_sat s' a'.
intros.
inversion H0. subst a. inversion H. split.
 trivial.
 exists v. exists s0. auto. 
Save.

Lemma sem_unpush : forall a a' b b' s ty,
  stack_sat s a' ->
  V.unpush class ty (b,a) = Some (b',a') ->
  b = b' /\ forall v, rt_ty_sat v ty -> stack_sat (v::s) a.
intros. 
simpl in H0. destruct a. discriminate.
destruct_bool (V.value_assertion_implication_dec class ty v) H1 H0.
inversion H0. subst a b. split.
 trivial. 
 intros. apply stk_sat_cons.
  eapply value_assertion_implication_sound. apply V.value_assertion_implication_dec_sound. apply H1. assumption.
  assumption.
Save.

Lemma sem_known_unpush : forall a a' b b' s ty,
  stack_sat s a' ->
  V.unpush_2 (b,a) = Some (ty, (b',a')) ->
  b = b' /\ forall v, rt_ty_sat v ty -> stack_sat (v::s) a.
intros. simpl V.unpush_2 in H0. destruct a.
 discriminate.
 inversion H0. split.
  reflexivity.
  intros. apply stk_sat_cons; assumption.
Save.

Lemma lvar_update : forall l a a' n t t',
  list_update a n t = Some a' ->
  lvar_sat l a' -> nth_error a n = Some t' ->
  V.value_assertion_implication class t t' -> lvar_sat l a.
intros. generalize a' a l H H0 H1. clear a' a l H H0 H1. 
induction n; intros; destruct a; try discriminate.
inversion H. inversion H1. inversion H0; subst.
discriminate.
inversion H0. apply lvar_sat_cons1. eapply value_assertion_implication_sound. apply H2. apply H9. apply H11.
inversion H0. subst. inversion H2. subst. apply lvar_sat_cons2. assumption.
rewrite (V.value_assertion_implication_top class t' H2). apply lvar_sat_cons2. apply H6.

simpl in H. destruct_opt (list_update a n t) H3 H. 
inversion H. subst. inversion H1. inversion H0. 
apply lvar_sat_cons1; eauto. 
apply lvar_sat_cons2; eauto. 
Save.

Lemma sem_lvar_lookup : forall l a n t,
  lvar_sat l a -> nth_error a n = Some t -> t<>C.A.va_top ->
  exists v, option_mult (nth_error l n) = Some v /\ rt_ty_sat v t.
intros. generalize a l H H0. clear a l H H0.
induction n; intros; destruct a; try discriminate; destruct l; inversion H; subst.
 inversion H0. subst t. exists v0. split; auto. 
 inversion H0. subst t. elimtype False. apply H1. trivial.
 simpl in *. eauto. 
 simpl in *. eauto. 
Save.

(*Lemma sem_unretrieve : forall a a' l b b' t n,
  lvar_sat l a' -> V.unretrieve class (V.stack_type_to_value_assertion t) n (a,b) = Some (a',b') ->
  b = b' /\ exists v, rt_ty_sat v (V.stack_type_to_value_assertion t) /\ option_mult (nth_error l n) = Some v /\ lvar_sat l a.*)

Lemma merge_not_top : forall a b c,
  a <> PreV.VA.va_top ->   (* TODO: if this is C.A.va_top, then it fails to typecheck at the end *)
  V.value_assertion_merge class a b = Some c ->
  c <> PreV.VA.va_top.
intros. unfold V.value_assertion_merge in H0.
destruct a; destruct b; first
 [ inversion H0; unfold not; intro; discriminate
 | inversion H0; assumption
 | idtac ].
destruct (V.value_assertion_implication_dec class (PreV.VA.va_addr t) (PreV.VA.va_addr t0)). 
 inversion H0. unfold not; intro; discriminate.
 destruct (V.value_assertion_implication_dec class (PreV.VA.va_addr t0) (PreV.VA.va_addr t));
  inversion H0; unfold not; intro; discriminate.
Save. 
Implicit Arguments merge_not_top [a b c]. 

Lemma sem_unretrieve : forall a a' l b b' t n,
  t <> PreV.VA.va_top ->
  lvar_sat l a' -> V.unretrieve class t n (a,b) = Some (a',b') ->
  b = b' /\ exists v, rt_ty_sat v t /\ option_mult (nth_error l n) = Some v /\ lvar_sat l a.
intros a a' l b b' t n not_top H H0.
simpl in H0. 
destruct_opt (nth_error a n) H1 H0. simpl in H0.
destruct_opt (V.value_assertion_merge class t x) H2 H0. simpl in H0.
destruct_opt (list_update a n x0) H3 H0.
inversion H0. subst.
split.
 trivial.
 assert (nth_error a' n = Some x0).
  eapply list_update_nth_error. apply H3. 
 destruct (sem_lvar_lookup _ _ _ _ H H4 (merge_not_top not_top H2)) as [v [lookup_ok v_ok]]. 
 exists v. intuition.
  eapply value_assertion_implication_sound. eapply V.value_assertion_merge_p1. apply H2. apply v_ok.  
  eapply lvar_update; eauto. eapply V.value_assertion_merge_p2. apply H2.
Save.

Lemma lvar_sat_length : forall l b, lvar_sat l b -> length l = length b.
intros. generalize b H. clear b H. induction l; intros; destruct b; inversion H.
trivial. simpl. rewrite (IHl b H5). trivial.
simpl. rewrite (IHl b H1). trivial.
Save.

Lemma lvar_update_prop : forall lv v l' n t x l,
  lvar_sat lv l' -> nth_error l n = Some t -> list_update l n x = Some l' -> rt_ty_sat v t ->
  exists lv', list_update lv n (Some v) = Some lv' /\ lvar_sat lv' l.
intros lv v. 
induction lv; intros; inversion H; subst; destruct l; destruct n; try discriminate; simpl in * |- *.
destruct (list_update l n x); discriminate.
inversion H1. inversion H0. subst. 
exists (Some v::lv). split. trivial. constructor; assumption. 
destruct_opt (list_update l n x) H3 H1. inversion H1. subst. 
destruct (IHlv _ _ _ _ _ H7 H0 H3 H2). destruct H4. rewrite H4.
exists (Some v0::x0). split. trivial. constructor; assumption.
inversion H1. inversion H0. subst. 
exists (Some v::lv). split. trivial. constructor; assumption. 
destruct_opt (list_update l n x) H3 H1. inversion H1. subst. 
destruct (IHlv _ _ _ _ _ H6 H0 H3 H2). destruct H4. rewrite H4.
exists (None::x0). split. trivial. constructor; assumption.
Save.
Implicit Arguments lvar_update_prop [lv v l' n t x l].

Lemma lvar_update_prop_2 : forall lv l n,
  lvar_sat lv l -> nth_error l n = Some PreV.VA.va_top ->
  exists lv', list_update lv n None = Some lv' /\ lvar_sat lv' l.
intro lv. 
induction lv; intros; inversion H; subst; destruct n; try discriminate; simpl in * |- *.
exists (None::lv). split. trivial. inversion H0. constructor. assumption.
destruct (IHlv _ _ H5 H0). destruct H1. rewrite H1. 
exists (Some v::x). split. trivial. constructor; assumption.
exists (None::lv). intuition. 
destruct (IHlv _ _ H4 H0). destruct H1. rewrite H1.
exists (None::x). intuition. constructor. assumption.
Save.
Implicit Arguments lvar_update_prop_2 [lv l n].

Lemma lvar_update_prop_3 : forall lv l' l n x,
  lvar_sat lv l' -> list_update l (S n) x = Some l' -> exists v, nth_error lv n = Some v.
intros.
apply nth_error_ok. 
rewrite (lvar_sat_length lv l' H). 
assert (S n < length l'). eapply list_update_lt_length_2. apply H0.
omega.
Save.
Implicit Arguments lvar_update_prop_3 [lv l' l n x].

Lemma lvar_sat_ty_sat : forall lv n v t l,
  nth_error lv n = Some (Some v) -> lvar_sat lv l -> nth_error l n = Some t -> rt_ty_sat v t.
intro. induction lv; intros; destruct n; destruct l; inversion H1; try discriminate; subst.
inversion H0. inversion H. subst. inversion H9. subst. assumption. 
apply ty_sat_top.
inversion H0; inversion H; subst; apply (IHlv n v t l); assumption.
Save.

Lemma is_va_top : forall v t,
  E.val_category v = C.category2 ->
  rt_ty_sat v t -> V.value_assertion_implication_dec class t PreV.VA.va_cat2 = false ->
  t = PreV.VA.va_top.
intros.
destruct v; destruct t; try discriminate; inversion H0; reflexivity.
Save.

Lemma va_category2 : forall v,
  rt_ty_sat v PreV.VA.va_cat2 -> E.val_category v = C.category2.
intros. destruct v; inversion H; reflexivity.
Save.

Lemma rt_ty_sat_category2 : forall v,
  E.val_category v = C.category2 -> rt_ty_sat v PreV.VA.va_cat2.
intros. destruct v; inversion H; auto. 
Save.

Lemma va_category1 : forall v,
  rt_ty_sat v C.A.va_cat1 -> E.val_category v = C.category1.
intros. destruct v; inversion H; reflexivity.
Save.

Lemma rt_ty_sat_category1 : forall v,
  E.val_category v = C.category1 -> rt_ty_sat v C.A.va_cat1.
intros. destruct v; inversion H; auto. 
Save.

Lemma va_notimp_category1 : forall v t, t <> C.A.va_top ->
  rt_ty_sat v t -> V.value_assertion_implication_dec class t PreV.VA.va_cat2 = false -> E.val_category v = C.category1.
intros.
destruct v; destruct t; inversion H0; try trivial; try discriminate;
 elimtype False; apply H; reflexivity.
Save.

Lemma va_not_top : forall v s,
  V.value_assertion_implication_dec class v (V.stack_type_to_value_assertion s) = true ->
  v <> C.A.va_top.
intros v s imp_s. 
destruct v; try (unfold not; intro; discriminate).
destruct s; discriminate.
Save.
Implicit Arguments va_not_top [v s].

(*
Lemma extend_va_imp_false : forall t1 t2,
  t1 <> V.E.R.C.va_top ->
  ~(V.value_assertion_implication class t2 V.va_cat2) ->
  V.value_assertion_implication class t1 t2 ->
  ~(V.value_assertion_implication class t1 V.va_cat2).
intros. unfold not. intro. apply H0. 
destruct t2; destruct t1; first
[assumption
|match reverse goal with H0:(V.value_assertion_implication class ?A ?B) |- _ => 
  assert (X:V.value_assertion_implication_dec class A B = false);
  [reflexivity|rewrite (V.value_assertion_implication_dec_complete class A B H0) in X; discriminate ] end
|constructor
|idtac].
*)

Lemma sem_unstore : forall lv l l' s s' n t is_cat2,
  lvar_sat lv l' -> V.unstore class n (l,s) is_cat2 = Some (t, (l', s')) ->
  s = s' /\
  forall v,
    rt_ty_sat v t ->
    (is_cat2 = true -> E.val_category v = C.category2) ->
    (is_cat2 = false -> E.val_category v = C.category1) ->
    exists lv', E.update_lvars n v lv = Some lv' /\ lvar_sat lv' l.
intros lv l l' s s' n t is_cat2 l'_ok unstore_code. 
unfold V.unstore in unstore_code.
destruct_opt (match n with O => ret tt | S nm1 => tnm1 <- nth_error l nm1;: if V.value_assertion_implication_dec class tnm1 PreV.VA.va_cat2 then fail else ret tt end) H unstore_code.
destruct_opt (nth_error l n) H0 unstore_code.
unfold bind in unstore_code.
destruct_bool is_cat2 H1 unstore_code.
 (* The found va is cat2 *)
 destruct_opt (nth_error l (S n)) H2 unstore_code.
  (* next position exists *)
  destruct (PreV.VA.value_assertion_eq_dec x1 PreV.VA.va_top).
   (* and contains va_top *)
   simpl in unstore_code.
   destruct_opt (list_update l n PreV.VA.va_top) H3 unstore_code.
   inversion unstore_code. subst. clear unstore_code.
   split.
    reflexivity.
    intros. 
    unfold E.update_lvars. 
    rewrite (H4 (refl_equal true)). 
    destruct (lvar_update_prop l'_ok H0 H3 H1) as [lv' [list_update_ok l_ok]].
    destruct (lvar_update_prop_2 l_ok H2) as [lv'' [list_update2_ok l_ok2]].
    destruct n. 
     rewrite list_update_ok. rewrite list_update2_ok. exists lv''. auto.
     destruct (lvar_update_prop_3 l'_ok H3) as [v' lookup_n_ok]. 
     rewrite lookup_n_ok. destruct v' as [r|].
      destruct r; unfold E.val_category; first [
       rewrite list_update_ok; rewrite list_update2_ok; exists lv''; auto
      |match goal with _:nth_error lv n = Some (Some ?v) |- _ => pose (v':=v) end;
       destruct_opt (nth_error l n) H6 H;
       unfold bind in H;
       destruct_bool (V.value_assertion_implication_dec class x0 PreV.VA.va_cat2) H7 H;
       assert (nth_error l' n = Some x0);
       [eapply list_update_indep; eauto with arith
       |assert (rt_ty_sat v' x0);
        [eapply lvar_sat_ty_sat; eauto
        |assert (x0 = PreV.VA.va_top);
         [apply (is_va_top v'); auto
         |subst;
          destruct (lvar_update_prop_2 l'_ok H8) as [lv1' [update1_ok l_ok']];
          destruct (lvar_update_prop l_ok' H0 H3 H1) as [lv1'' [update2_ok l_ok'']];
          destruct (lvar_update_prop_2 l_ok'' H2) as [lv1''' [update3_ok l_ok''']];
          exists lv1'''; rewrite update1_ok; rewrite update2_ok; rewrite update3_ok; auto ]]]]. 
      rewrite list_update_ok. rewrite list_update2_ok. exists lv''. auto.
  (* next position does not exist: not possible *)
  discriminate. 
 (* The found va is possibly not cat2 *)
 destruct_opt (list_update l n PreV.VA.va_top) H2 unstore_code.
 inversion unstore_code. subst. clear unstore_code.
 split. reflexivity.
  intros.
  unfold E.update_lvars. rewrite (H4 (refl_equal false)). destruct n.
   destruct (lvar_update_prop l'_ok H0 H2 H1) as [lv' [update_ok lv'_ok]]. rewrite update_ok. exists lv'. auto.
   destruct (lvar_update_prop_3 l'_ok H2) as [v' v'_exists].
   rewrite v'_exists. destruct v' as [r|].
    destruct r; unfold E.val_category; first
    [destruct (lvar_update_prop l'_ok H0 H2 H1) as [lv' [update_ok lv'_ok]]; rewrite update_ok; exists lv'; auto
    |match goal with _:nth_error lv n = Some (Some ?v) |- _ => pose (v':=v) end;
     destruct_opt (nth_error l n) H5 H;
     unfold bind in H;
     destruct_bool (V.value_assertion_implication_dec class x0 PreV.VA.va_cat2) H6 H;
     assert (nth_error l' n = Some x0);
     [eapply list_update_indep; eauto with arith
     |assert (rt_ty_sat v' x0);
      [eapply lvar_sat_ty_sat; eauto
      |assert (x0 = PreV.VA.va_top);
       [apply (is_va_top v'); auto
       |subst;
        destruct (lvar_update_prop_2 l'_ok H7) as [lv1' [update1_ok l_ok']];
        destruct (lvar_update_prop l_ok' H0 H2 H1) as [lv1'' [update2_ok l_ok'']];
        exists lv1''; rewrite update1_ok; rewrite update2_ok; auto ]]]]. 
    destruct (lvar_update_prop l'_ok H0 H2 H1) as [lv' [update_ok l_ok']]. rewrite update_ok. exists lv'. auto.
Save.  

(*
Lemma sem_unstore : forall lv l l' s s' n t,
  lvar_sat lv l' -> V.unstore class n t (l,s) = Some (l',s') ->
  s = s' /\ forall v, rt_ty_sat v t -> exists lv', V.E.update_lvars n v lv = Some lv' /\ lvar_sat lv' l.
intros. 
unfold V.unstore in H0. 
destruct (V.value_assertion_eq_dec t V.E.R.C.va_top). discriminate.
destruct_opt (match n with O => ret tt | S nm1 => tnm1 <- nth_error l nm1;: if V.value_assertion_implication_dec class tnm1 V.va_cat2 then fail else ret tt end) H1 H0.
destruct_opt (nth_error l n) H2 H0. 
unfold bind in H0. 
destruct_bool (V.value_assertion_implication_dec class t x0) H3 H0.
destruct_bool (V.value_assertion_implication_dec class t V.va_cat2) H4 H0.
(* Case when it is a category2 value being 'unstored' *)
destruct_opt (nth_error l (S n)) H5 H0.
destruct (V.value_assertion_eq_dec x1 V.E.R.C.va_top); try discriminate.
destruct_opt (list_update l n V.E.R.C.va_top) H6 H0.
inversion H0. subst. clear H0. 
split.
 trivial.
 intros. 
 unfold V.E.update_lvars. rewrite va_category2. 
 assert (rt_ty_sat v x0). eapply value_assertion_implication_sound. apply V.value_assertion_implication_dec_sound. apply H3. apply H0.
 destruct n. 
  destruct (lvar_update_prop _ _ _ _ _ _ _ H H2 H6 H7). destruct H8. rewrite H8. 
  destruct (lvar_update_prop_2 _ _ _ H9 H5). destruct H10. rewrite H10.
  exists x2. intuition. 
  destruct_opt (nth_error l n) H8 H1.
  unfold bind in H1. destruct_bool (V.value_assertion_implication_dec class x1 V.va_cat2) H9 H1. 
  destruct (lvar_update_prop_3 _ _ _ _ _ H H6). rewrite H10. destruct x2. 
   (* something exists in the previous slot *)
   destruct r; unfold V.E.val_category; try
    (destruct (lvar_update_prop _ _ _ _ _ _ _ H H2 H6 H7); destruct H11; rewrite H11; 
     destruct (lvar_update_prop_2 _ _ _ H12 H5); destruct H13; rewrite H13;
     exists x3; intuition).
   (* longs *)
   assert (nth_error l' n = Some x1). eapply list_update_indep. apply H8. apply H6. auto with arith.
   assert (rt_ty_sat V.E.rt_long x1). eapply lvar_sat_ty_sat. apply H10. apply H. assumption.
   assert (x1 = V.E.R.C.va_top). apply (is_va_top V.E.rt_long). trivial. assumption. unfold not. intro. rewrite (V.value_assertion_implication_dec_complete class _ _ H13) in H9. discriminate.  
   subst. 
   destruct (lvar_update_prop_2 _ _ _ H H11). destruct H13. rewrite H13.
   destruct (lvar_update_prop _ _ _ _ _ _ _ H14 H2 H6 H7). destruct H15. rewrite H15. 
   destruct (lvar_update_prop_2 _ _ _ H16 H5); destruct H17; rewrite H17;
   exists x3; intuition.
   (* doubles *)
   assert (nth_error l' n = Some x1). eapply list_update_indep. apply H8. apply H6. auto with arith.
   assert (rt_ty_sat V.E.rt_double x1). eapply lvar_sat_ty_sat. apply H10. apply H. assumption.
   assert (x1 = V.E.R.C.va_top). apply (is_va_top V.E.rt_double). trivial. assumption. unfold not. intro. rewrite (V.value_assertion_implication_dec_complete class _ _ H13) in H9. discriminate.  
   subst. 
   destruct (lvar_update_prop_2 _ _ _ H H11). destruct H13. rewrite H13.
   destruct (lvar_update_prop _ _ _ _ _ _ _ H14 H2 H6 H7). destruct H15. rewrite H15. 
   destruct (lvar_update_prop_2 _ _ _ H16 H5); destruct H17; rewrite H17;
   exists x3; intuition.
   destruct (lvar_update_prop _ _ _ _ _ _ _ H H2 H6 H7); destruct H11; rewrite H11; 
   destruct (lvar_update_prop_2 _ _ _ H12 H5); destruct H13; rewrite H13;
   exists x3; intuition.
eapply value_assertion_implication_sound. 
 apply V.value_assertion_implication_dec_sound. apply H4. 
 apply H0.
(* Case for a category1 value *)
destruct_opt (list_update l n V.E.R.C.va_top) H5 H0.
inversion H0. subst. clear H0. 
split.
 trivial. 
 intros. 
 assert (V.E.val_category v = V.E.R.C.category1). eapply va_notimp_category1. apply n0. apply H0. 
  unfold not. intros. rewrite (V.value_assertion_implication_dec_complete class _ _ H6) in H4. discriminate.
 assert (rt_ty_sat v x0). eapply value_assertion_implication_sound. apply V.value_assertion_implication_dec_sound. apply H3. apply H0.
 unfold V.E.update_lvars. rewrite H6.
 destruct n.
  destruct (lvar_update_prop _ _ _ _ _ _ _ H H2 H5 H7). destruct H8. rewrite H8. exists x1. intuition. 
  destruct_opt (nth_error l n) H8 H1. 
  unfold bind in H1. destruct_bool (V.value_assertion_implication_dec class x1 V.va_cat2) H9 H1.
  destruct (lvar_update_prop_3 _ _ _ _ _ H H5). rewrite H10. destruct x2. 
   destruct r; unfold V.E.val_category; try
    (destruct (lvar_update_prop _ _ _ _ _ _ _ H H2 H5 H7); destruct H11; rewrite H11; 
     exists x2; intuition).
   (* case for long *)
   assert (nth_error l' n = Some x1). eapply list_update_indep. apply H8. apply H5. auto with arith.
   assert (rt_ty_sat V.E.rt_long x1). eapply lvar_sat_ty_sat. apply H10. apply H. assumption.
   assert (x1 = V.E.R.C.va_top). apply (is_va_top V.E.rt_long). trivial. assumption. unfold not. intro. rewrite (V.value_assertion_implication_dec_complete class _ _ H13) in H9. discriminate.  
   subst. 
   destruct (lvar_update_prop_2 _ _ _ H H11). destruct H13. rewrite H13. 
   destruct (lvar_update_prop _ _ _ _ _ _ _ H14 H2 H5 H7). destruct H15. rewrite H15.
   exists x2. auto.
   (* case for double *)
   assert (nth_error l' n = Some x1). eapply list_update_indep. apply H8. apply H5. auto with arith.
   assert (rt_ty_sat V.E.rt_double x1). eapply lvar_sat_ty_sat. apply H10. apply H. assumption.
   assert (x1 = V.E.R.C.va_top). apply (is_va_top V.E.rt_double). trivial. assumption. unfold not. intro. rewrite (V.value_assertion_implication_dec_complete class _ _ H13) in H9. discriminate.  
   subst. 
   destruct (lvar_update_prop_2 _ _ _ H H11). destruct H13. rewrite H13. 
   destruct (lvar_update_prop _ _ _ _ _ _ _ H14 H2 H5 H7). destruct H15. rewrite H15.
   exists x2. auto.
   destruct (lvar_update_prop _ _ _ _ _ _ _ H H2 H5 H7). destruct H11. rewrite H11. 
   exists x2. auto. 
Save.
*)

Lemma sem_pop_n : forall A A' s,
  stack_sat s (A ++ A') ->
  exists l, exists l', E.pop_n (length A) s = Some (l,l') /\ stack_sat_exact l A /\ stack_sat l' A'.
intros A A'. induction A; intros.
 exists (nil (A:=E.rt_val)). exists s. intuition. constructor. 
 destruct s; inversion H. subst. destruct (IHA s H5). destruct H0. 
 exists (r::x). exists x0. intuition.
  simpl. rewrite H1. reflexivity.
  constructor; assumption.
Save.

Lemma general_lvars_sat : forall n, lvar_sat (E.make_padding_lvars n) (V.general_lvar_assertion n).
intro. induction n; simpl; constructor. assumption.
Save.

Lemma java_type_category1 : forall v ty, rt_ty_sat v (V.java_type_to_value_assertion ty) -> C.java_type_category ty = C.category1 -> E.val_category v = C.category1.
intros. 
apply va_category1. 
eapply value_assertion_implication_sound. 
apply V.java_type_category_correct1. 
apply H0. assumption.
Save.

Lemma java_type_category2 : forall v ty, rt_ty_sat v (V.java_type_to_value_assertion ty) -> C.java_type_category ty = C.category2 -> E.val_category v = C.category2.
intros. 
apply va_category2. 
eapply value_assertion_implication_sound. 
apply V.java_type_category_correct2. 
apply H0. assumption.
Save.

Lemma sem_argument_prep : forall arg_types s l n,
  V.arg_tys_to_lvar_assertion arg_types n = Some l ->
  stack_sat_exact s (map V.java_type_to_value_assertion arg_types) ->
  exists lv, E.stack_to_lvars s n = Some lv /\
             lvar_sat lv l.
intro. induction arg_types; intros.
 simpl in * |- *. inversion H. inversion H0. subst.
 exists (E.make_padding_lvars n). intuition. apply general_lvars_sat.
 simpl in * |- *. 
 inversion H0. subst.
 generalize (refl_equal (V.C.java_type_category a)); pattern (V.C.java_type_category a) at -1; case (V.C.java_type_category a); intros; rewrite H1 in H.
  destruct (O_or_S n). 
   destruct s. rewrite <- e in H. 
   destruct_opt (V.arg_tys_to_lvar_assertion arg_types x) H2 H. inversion H. subst.
   destruct (IHarg_types _ _ _ H2 H5). destruct H3. exists (Some v::x1). split.
    simpl. rewrite (java_type_category1 _ _ H4 H1). rewrite H3. reflexivity.
    constructor; assumption.
   subst. discriminate.
  destruct (O_or_S n).
   destruct s. subst. destruct (O_or_S x). 
    destruct s. subst. destruct_opt (V.arg_tys_to_lvar_assertion arg_types x0) H2 H. inversion H. subst.
    destruct (IHarg_types _ _ _ H2 H5). destruct H3. exists (Some v::None::x1). split.
     simpl. rewrite (java_type_category2 _ _ H4 H1). rewrite H3. reflexivity.
     constructor. assumption. constructor. assumption.
    subst. discriminate.
   subst. discriminate.
Save.

Lemma stack_sat_exact_app : forall s1 a1 s2 a2, stack_sat_exact s1 a1 -> stack_sat_exact s2 a2 -> stack_sat_exact (s1++s2) (a1++a2).
intros. generalize a1 H. clear a1 H.
induction s1; intros; destruct a1; inversion H; subst; simpl.
 assumption.
 constructor; auto.
Save.

Lemma stack_sat_exact_rev : forall s a, stack_sat_exact s a -> stack_sat_exact (rev s) (rev a).
intro. induction s; intros; inversion H; subst; simpl.
 constructor. 
 apply stack_sat_exact_app. auto. constructor. assumption. constructor.
Save.

Lemma stack_sat_exact_rev_2 : forall s a, stack_sat_exact s (rev a) -> stack_sat_exact (rev s) a.
intros. replace a with (rev (rev a)). apply stack_sat_exact_rev. assumption. apply rev_involutive.
Save.

Lemma lvar_sat_app : forall l1 a1 l2 a2, lvar_sat l1 a1 -> lvar_sat l2 a2 -> lvar_sat (l1++l2) (a1++a2).
intros. generalize a1 H. clear a1 H.
induction l1; intros; destruct a1; inversion H.
simpl. assumption. 
simpl. apply lvar_sat_cons1. apply H4. apply IHl1. apply H6. 
simpl. apply lvar_sat_cons2. apply IHl1. apply H2.
Save.

Lemma lvar_sat_rev : forall l a, lvar_sat l a -> lvar_sat (rev l) (rev a).
intros. generalize a H. clear a H.
induction l; intros. destruct a; inversion H.
apply lvar_sat_nil.
destruct a0; inversion H.
simpl. apply lvar_sat_app. apply IHl. apply H5. apply lvar_sat_cons1. apply H3. apply lvar_sat_nil.
simpl. apply lvar_sat_app. apply IHl. apply H1. apply lvar_sat_cons2. apply lvar_sat_nil.
Save.

Lemma default_value_sat : forall j, rt_ty_sat (E.default_value j) (V.java_type_to_value_assertion j).
intros. destruct j; simpl; try constructor.
Save.

End Satisfiability.

Definition preserve_heap_types := fun heap1 heap2 =>
  forall a nm fields,
    E.ObjectHeap.lookup heap1 a = Some (E.hp_object nm fields) ->
    exists fields', E.ObjectHeap.lookup heap2 a = Some (E.hp_object nm fields').

Lemma preserve_heap_types_id : forall h, preserve_heap_types h h.
unfold preserve_heap_types. intros.
exists fields. assumption.
Save.
Hint Resolve preserve_heap_types_id.

Lemma preserve_old_classes_id : forall c, E.R.preserve_old_classes c c.
intros. unfold E.R.preserve_old_classes. auto.
Save.
Hint Resolve preserve_old_classes_id.

Lemma preserve_heap_types_trans : forall heapA heapB heapC,
  preserve_heap_types heapA heapB ->
  preserve_heap_types heapB heapC ->
  preserve_heap_types heapA heapC.
unfold preserve_heap_types. intros. 
destruct (H _ _ _ H1).
apply (H0 _ _ _ H2).
Save.

Lemma preserve_rt_ty_sat : forall classesA classesB heapA heapB v a,
  rt_ty_sat classesA heapA v a ->
  E.R.preserve_old_classes classesA classesB ->
  preserve_heap_types heapA heapB ->
  rt_ty_sat classesB heapB v a.
intros. induction H; try constructor.
 destruct (H1 _ _ _ H); eapply ty_sat_addr2;
 [apply H3|eapply R.preserve_subclass; [apply H2|apply H0]].
 destruct (H1 _ _ _ H); eapply ty_sat_ref_Some. eauto.
Save.

Lemma preserve_lvar_sat : forall classesA classesB heapA heapB lvars a,
  lvar_sat classesA heapA lvars a ->
  R.preserve_old_classes classesA classesB ->
  preserve_heap_types heapA heapB ->
  lvar_sat classesB heapB lvars a.
intros. induction H. 
 constructor. 
 apply lvar_sat_cons1. 
  eapply preserve_rt_ty_sat. 
   apply H.
   apply H0.
   apply H1.
  apply IHlvar_sat.
 apply lvar_sat_cons2.
  apply IHlvar_sat.
Save.

Lemma preserve_stack_sat : forall classesA classesB heapA heapB stack a,
  stack_sat classesA heapA stack a ->
  R.preserve_old_classes classesA classesB ->
  preserve_heap_types heapA heapB ->
  stack_sat classesB heapB stack a.
intros. induction H.
 constructor.
 apply stk_sat_cons. 
  eapply preserve_rt_ty_sat.
   apply H.
   apply H0.
   apply H1.
  apply IHstack_sat.
Save.

Lemma preserve_stack_sat_exact : forall classesA classesB heapA heapB stack a,
  stack_sat_exact classesA heapA stack a ->
  R.preserve_old_classes classesA classesB ->
  preserve_heap_types heapA heapB ->
  stack_sat_exact classesB heapB stack a.
intros. induction H.
 constructor.
 apply stk_sat_exact_cons. 
  eapply preserve_rt_ty_sat.
   apply H.
   apply H0.
   apply H1.
  apply IHstack_sat_exact.
Save.
Implicit Arguments preserve_stack_sat_exact [classesA classesB heapA heapB stack a].

Lemma preserve_subclass_assertions_satisfied : forall classesA classesB class,
  subclass_assertions_satisfied classesA class ->
  R.preserve_old_classes classesA classesB ->
  subclass_assertions_satisfied classesB class.
unfold subclass_assertions_satisfied. intros. 
eapply R.preserve_subclass. 
 apply H. apply H1.
 apply H0.
Save.

Lemma sem_unpush_2 : forall classes heap class a a' b b' s ty,
  subclass_assertions_satisfied classes class ->
  stack_sat classes heap s a' ->
  V.unpush class ty (b,a) = Some (b',a') ->
  b = b' /\ forall v classes' heap',
   R.preserve_old_classes classes classes' ->
   preserve_heap_types heap heap' ->
   rt_ty_sat classes' heap' v ty -> stack_sat classes' heap' (v::s) a.
intros. 
simpl in H1. destruct a. discriminate.
destruct_bool (V.value_assertion_implication_dec class ty v) H2 H1.
inversion H1. subst a b. split.
 trivial. 
 intros. apply stk_sat_cons.
  eapply value_assertion_implication_sound. 
   eapply preserve_subclass_assertions_satisfied; eauto.
   apply V.value_assertion_implication_dec_sound. apply H2. assumption.
  eapply preserve_stack_sat; eauto.
Save.
Implicit Arguments sem_unpush_2 [classes heap class a a' b b' s ty].


Implicit Arguments sem_unpop [classes heap s a a' b b' ty].
Implicit Arguments sem_unpush [classes heap class a a' b b' s ty].
Implicit Arguments sem_known_unpush [classes heap a a' b b' s ty].
Implicit Arguments sem_lvar_lookup [classes heap l a n t].
Implicit Arguments sem_unretrieve [classes heap class a a' l b b' t n].
Implicit Arguments sem_unstore [classes heap class lv l l' s s' n t is_cat2].
Implicit Arguments sem_pop_n [classes heap A A' s].
Implicit Arguments sem_argument_prep [classes heap class arg_types s l n].

Lemma check_exception_handlers_prop : forall classes heap code class cert pc (handlers:list C.exception_handler) e e_exists res l,
  subclass_assertions_satisfied classes class ->
  R.sub_class classes (C.class_name e) B.java_lang_Exception ->
  V.check_exception_handlers code class cert pc handlers = Some l ->
  E.search_handlers classes handlers pc class e e_exists = res ->
  (exists pc', exists l', exists s',
    E.handler_found pc' = res /\
    PreV.VA.Cert.lookup cert pc' = Some (l', s') /\
    V.lvar_assertion_implication class l l' /\
    forall v, rt_ty_sat classes heap v (PreV.VA.va_addr (C.class_name e)) -> stack_sat classes heap (v::nil) s')
  \/
  E.handler_notfound = res.
intros classes heap code class cert pc handlers e e_exists res.  
induction handlers.
 (* Base case: no handlers *)
 simpl in *. intros l subclassing_ok e_isa_Throwable check_code search_code.
 right. assumption.
 (* Step case *)
 intros l subclassing_ok e_isa_Throwable check_code search_code.
 destruct a as [start_pc end_pc handler_pc opt_type_idx]. 
 simpl in *.
 destruct (option_dec (V.check_exception_handlers code class cert pc handlers)) as [[l' handlers_checked] | checkfailed].
  (* Checking the rest succeeded *)
  rewrite handlers_checked in check_code.
  simpl in check_code. 
  change (E.R.C.is_within start_pc end_pc pc) with (V.C.is_within start_pc end_pc pc) in search_code.
  destruct (V.C.is_within start_pc end_pc pc) as [is_within | is_without]. 
   (* This handler applies to this pc *)
   destruct (option_dec (PreV.VA.Cert.lookup cert handler_pc)) as [[[handler_l handler_s] cert_lookup_ok] | cert_lookup_failed].
    (* Certificate lookup succeeded *)
    rewrite cert_lookup_ok in check_code. simpl in check_code.
    destruct opt_type_idx as [idx|].
     (* This handler is for a specific type *)
     (*change (match E.R.C.ConstantPool.lookup (E.R.C.class_constantpool class) idx
             with
             | Some o =>
             match o with
             | E.R.C.cpe_methodref _ _ _ => E.handler_wrong
             | E.R.C.cpe_fieldref _ _ _ => E.handler_wrong
             | E.R.C.cpe_int _ => E.handler_wrong
             | E.R.C.cpe_classref cls_nm =>
                 if E.R.check_subclass e_exists cls_nm
                 then E.handler_found handler_pc
                 else
                  E.search_handlers classes handlers pc class e e_exists
             | E.R.C.cpe_other => E.handler_wrong
             end
             | None => E.handler_wrong end)
       with (match V.C.ConstantPool.lookup (V.C.class_constantpool class) idx
             with
             | Some o =>
             match o with
             | V.C.cpe_classref cls_nm => if E.R.check_subclass e_exists cls_nm
                 then E.handler_found handler_pc
                 else
                  E.search_handlers classes handlers pc class e e_exists
             | _ => E.handler_wrong
             end
             | None => E.handler_wrong end) in search_code.*)
     destruct (option_dec (V.C.ConstantPool.lookup (V.C.class_constantpool class) idx)) as [[ref constantpool_ok] | constantpool_fail].
      (* constant pool lookup succeded *)
      rewrite constantpool_ok in check_code. 
      change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in constantpool_ok.
      change V.C.class_constantpool with E.R.C.class_constantpool in constantpool_ok.
      rewrite constantpool_ok in search_code. 
      simpl in check_code. 
      destruct ref as [x|x|x|clsname|]; try discriminate.
      unfold ret in check_code.
      unfold bind in check_code.
      destruct (bool_dec (V.stack_assertion_implication_dec class (PreV.VA.va_addr clsname::nil) handler_s)) as [imp_ok|imp_notok].
       (* Stack implication ok *)
       rewrite imp_ok in check_code. simpl in check_code.
       destruct (bool_dec (E.R.check_subclass e_exists clsname)) as [e_isa_clsname|not_e_isa_clsname].
        (* This handler is actually the one we want *)
        rewrite e_isa_clsname in search_code. 
        left. exists handler_pc. exists handler_l. exists handler_s. intuition.
         eapply V.lvar_assertion_merge_p2. apply check_code.
         eapply stack_assertion_implication_sound. 
          apply subclassing_ok.
          apply V.stack_assertion_implication_dec_sound. apply imp_ok.
          apply stk_sat_cons; try constructor.
           change (PreV.VA.va_addr (C.class_name e)) with (C.A.va_addr (C.class_name e)) in H1.
           inversion H1. 
           (* reference was null *)
           subst v x. apply ty_sat_addr1. 
           (* reference wasn't null *)
           subst v nm. eapply ty_sat_addr2. 
            apply H3. 
            eapply R.sub_class_trans. 
             apply H5.
             eapply R.check_subclass_sound. apply e_isa_clsname.
        (* not the handler we were looking for *)
        rewrite not_e_isa_clsname in search_code.
        destruct (IHhandlers l' subclassing_ok e_isa_Throwable handlers_checked search_code) as [[pc' [l'' [s'' [res_is_found [cert_lookup_ok' [lvar_imp_ok stk_ok]]]]]] | res_is_notfound].
         (* a handler was found *)
         left. exists pc'. exists l''. exists s''. intuition.
          eapply V.lvar_assertion_implication_trans. 
           eapply V.lvar_assertion_merge_p1. apply check_code.
           apply lvar_imp_ok.
         (* a handler was not found *)
         right. assumption.
       (* stack implication not ok *)
       rewrite imp_notok in check_code. discriminate.
      (* constantpool looked failed *)
      rewrite constantpool_fail in check_code. discriminate.
     (* Handler not for a specific type *)
     unfold ret in check_code. 
     unfold bind in check_code. 
     destruct (bool_dec (V.stack_assertion_implication_dec class (PreV.VA.va_addr V.B.java_lang_Exception :: nil) handler_s)) as [stk_imp_ok|stk_imp_notok].
      (* stack implication was ok *)
      rewrite stk_imp_ok in check_code.
      simpl in check_code.
      left. exists handler_pc. exists handler_l. exists handler_s. intuition.
       eapply V.lvar_assertion_merge_p2. apply check_code.
       eapply stack_assertion_implication_sound. 
        apply subclassing_ok. 
        apply V.stack_assertion_implication_dec_sound. apply stk_imp_ok.
        apply stk_sat_cons; try constructor.
         change (PreV.VA.va_addr (C.class_name e)) with (C.A.va_addr (C.class_name e)) in H1.
         inversion H1. 
         (* reference was null *)
         subst v x. apply ty_sat_addr1.
         (* reference wasn't null *)
         subst v nm. eapply ty_sat_addr2.
          apply H3.
          eapply R.sub_class_trans. 
           apply H5. 
           assumption.
      (* stack implication was not ok *)
      rewrite stk_imp_notok in check_code. discriminate.
    (* certificate lookup failed *)
    rewrite cert_lookup_failed in check_code. discriminate.
   (* Handler does not apply to this pc *)
   inversion check_code. subst l'. apply IHhandlers; assumption.
  (* checking the other handlers failed *)
  rewrite checkfailed in check_code. discriminate.
Save.

Inductive safe_current_frame (classes:R.cert_classpool) (heap:E.ObjectHeap.t) : E.frame -> option C.java_type -> Prop :=
  mk_safe_current_frame : forall cert op_stack lvars pc class rt lvar_assertion stack_assertion code,
    R.Classpool.lookup (R.classpool classes) (C.class_name class) = Some class ->
    V.safe_code code class rt cert  ->
    C.A.Cert.lookup cert pc = Some (lvar_assertion, stack_assertion) ->
    lvar_sat classes heap lvars lvar_assertion ->
    stack_sat classes heap op_stack stack_assertion ->
    subclass_assertions_satisfied classes class ->
    safe_current_frame classes heap (E.mkFrame op_stack lvars pc code class) rt.

Inductive safe_frame_stack (classes:R.cert_classpool) (heap:E.ObjectHeap.t) : list E.frame -> option C.java_type -> option C.java_type -> Prop :=
| safe_stack_nil  : forall rt, safe_frame_stack classes heap nil rt rt
| safe_stack_cons : forall op_stack lvars pc class fs in_ty out_ty final_ty cert lvar_assertion stack_assertion code lvar_exc_assertion,
    safe_frame_stack classes heap fs out_ty final_ty ->
    R.Classpool.lookup (R.classpool classes) (C.class_name class) = Some class ->
    V.safe_code code class out_ty cert ->
    C.A.Cert.lookup cert (S pc) = Some (lvar_assertion, stack_assertion) ->
    lvar_sat classes heap lvars lvar_assertion ->
    (forall v classes' heap',
       R.preserve_old_classes classes classes' ->
       preserve_heap_types heap heap' ->
       rt_ty_sat classes' heap' v (V.java_type_to_value_assertion in_ty) ->
       stack_sat classes' heap' (v::op_stack) stack_assertion) ->
    subclass_assertions_satisfied classes class ->
    V.check_exception_handlers code class cert pc (C.code_exception_table code) = Some lvar_exc_assertion ->
    lvar_sat classes heap lvars lvar_exc_assertion ->
    safe_frame_stack classes heap (E.mkFrame op_stack lvars pc code class::fs) (Some in_ty) final_ty
| safe_stack_cons_void : forall op_stack lvars pc class fs out_ty final_ty cert lvar_assertion stack_assertion code lvar_exc_assertion,
    safe_frame_stack classes heap fs out_ty final_ty ->
    R.Classpool.lookup (R.classpool classes) (C.class_name class) = Some class ->
    V.safe_code code class out_ty cert ->
    C.A.Cert.lookup cert (S pc) = Some (lvar_assertion, stack_assertion) ->
    lvar_sat classes heap lvars lvar_assertion ->
    stack_sat classes heap op_stack stack_assertion ->
    subclass_assertions_satisfied classes class ->
    V.check_exception_handlers code class cert pc (C.code_exception_table code) = Some lvar_exc_assertion ->
    lvar_sat classes heap lvars lvar_exc_assertion ->
    safe_frame_stack classes heap (E.mkFrame op_stack lvars pc code class::fs) None final_ty.

Inductive static_method_ref_resolvable : R.cert_classpool -> R.Preclasspool.t -> B.Classname.t -> B.Classname.t -> B.Methodname.t -> C.descriptor -> Prop :=
| mk_static_method_ref_resolvable : forall caller c_nm m_nm m_desc classes preclasses classes' p o c m H code,
    R.resolve_method caller c_nm m_nm m_desc classes preclasses = R.load_ok _ (classes':=classes') p o (c,m) H ->
    C.method_static m = true ->
    C.method_code m = Some code ->
    static_method_ref_resolvable classes preclasses caller c_nm m_nm m_desc.

Inductive instance_special_method_ref_resolvable : R.cert_classpool -> R.Preclasspool.t -> B.Classname.t -> B.Classname.t -> B.Methodname.t -> C.descriptor -> Prop :=
| mk_instance_special_method_ref_resolvable : forall caller c_nm m_nm m_desc classes preclasses classes' p o c m H code,
    R.resolve_method caller c_nm m_nm m_desc classes preclasses = R.load_ok _ (classes':=classes') p o (c,m) H ->
    C.method_static m = false ->
    C.method_abstract m = false ->
    C.method_code m = Some code ->
    instance_special_method_ref_resolvable classes preclasses caller c_nm m_nm m_desc.

Inductive instance_method_ref_resolvable : R.cert_classpool -> R.Preclasspool.t -> B.Classname.t -> B.Classname.t -> B.Methodname.t -> C.descriptor -> Prop :=
| mk_instance_method_ref_resolvable : forall caller c_nm m_nm m_desc classes preclasses classes' p o c m H,
    R.resolve_method caller c_nm m_nm m_desc classes preclasses = R.load_ok _ (classes':=classes') p o (c,m) H ->
    C.method_static m = false ->
    instance_method_ref_resolvable classes preclasses caller c_nm m_nm m_desc.

Inductive static_field_ref_resolvable : R.cert_classpool -> R.Preclasspool.t -> B.Classname.t -> B.Classname.t -> B.Fieldname.t -> C.java_type -> Prop :=
| mk_static_field_ref_resolvable : forall caller c_nm f_nm f_ty classes preclasses classes' p o c f H,
    R.resolve_field caller c_nm f_nm f_ty classes preclasses = R.load_ok _ (classes':=classes') p o (c,f) H ->
    C.field_static f = true ->
    static_field_ref_resolvable classes preclasses caller c_nm f_nm f_ty.

Inductive instance_field_ref_resolvable : R.cert_classpool -> R.Preclasspool.t -> B.Classname.t -> B.Classname.t -> B.Fieldname.t -> C.java_type -> Prop :=
| mk_instance_field_ref_resolvable : forall caller c_nm f_nm f_ty classes preclasses classes' p o c f H,
    R.resolve_field caller c_nm f_nm f_ty classes preclasses = R.load_ok _ (classes':=classes') p o (c,f) H ->
    C.field_static f = false ->
    C.field_final f = false ->
    instance_field_ref_resolvable classes preclasses caller c_nm f_nm f_ty.

Inductive instantiatable_class_ref_resolvable : R.cert_classpool -> R.Preclasspool.t -> B.Classname.t -> B.Classname.t -> Prop :=
| mk_instantiatable_class_ref_resolvable : forall caller c_nm classes preclasses classes' p o c H,
    R.resolve_class caller c_nm classes preclasses = R.load_ok _ (classes':=classes') p o c H ->
    C.class_interface c = false ->
    C.class_abstract c = false ->
    instantiatable_class_ref_resolvable classes preclasses caller c_nm.

Inductive class_ref_resolvable : R.cert_classpool -> R.Preclasspool.t -> B.Classname.t -> B.Classname.t -> Prop :=
| mk_class_ref_resolvable : forall caller c_nm classes preclasses classes' p o c H,
    R.resolve_class caller c_nm classes preclasses = R.load_ok _ (classes':=classes') p o c H ->
    class_ref_resolvable classes preclasses caller c_nm.

Inductive all_resolvable_for_class : R.cert_classpool -> R.Preclasspool.t -> C.class -> Prop :=
| mk_all_resolvable_for_class : forall classes preclasses class,
    (forall cp_idx c_nm m_nm m_desc,
       C.ConstantPool.lookup (C.class_constantpool class) cp_idx = Some (C.cpe_methodref c_nm m_nm m_desc) ->
       C.A.ConstantPoolAdditional.lookup (C.A.class_annot_constantpool (C.class_annotation class)) cp_idx = Some (C.A.cpae_static_method) ->
       static_method_ref_resolvable classes preclasses (C.class_name class) c_nm m_nm m_desc) ->
    (forall cp_idx c_nm m_nm m_desc,
       C.ConstantPool.lookup (C.class_constantpool class) cp_idx = Some (C.cpe_methodref c_nm m_nm m_desc) ->
       C.A.ConstantPoolAdditional.lookup (C.A.class_annot_constantpool (C.class_annotation class)) cp_idx = Some (C.A.cpae_instance_special_method) ->
       instance_special_method_ref_resolvable classes preclasses (C.class_name class) c_nm m_nm m_desc) ->
    (forall cp_idx c_nm m_nm m_desc,
       C.ConstantPool.lookup (C.class_constantpool class) cp_idx = Some (C.cpe_methodref c_nm m_nm m_desc) ->
       C.A.ConstantPoolAdditional.lookup (C.A.class_annot_constantpool (C.class_annotation class)) cp_idx = Some (C.A.cpae_instance_method) ->
       instance_method_ref_resolvable classes preclasses (C.class_name class) c_nm m_nm m_desc) ->
    (forall cp_idx c_nm f_nm f_ty,
       C.ConstantPool.lookup (C.class_constantpool class) cp_idx = Some (C.cpe_fieldref c_nm f_nm f_ty) ->
       C.A.ConstantPoolAdditional.lookup (C.A.class_annot_constantpool (C.class_annotation class)) cp_idx = Some (C.A.cpae_static_field) ->
       static_field_ref_resolvable classes preclasses (C.class_name class) c_nm f_nm f_ty) ->
    (forall cp_idx c_nm,
       C.ConstantPool.lookup (C.class_constantpool class) cp_idx = Some (C.cpe_classref c_nm) ->
          class_ref_resolvable classes preclasses (C.class_name class) c_nm
       /\ (C.A.ConstantPoolAdditional.lookup (C.A.class_annot_constantpool (C.class_annotation class)) cp_idx = Some (C.A.cpae_instantiable_class) ->
           instantiatable_class_ref_resolvable classes preclasses (C.class_name class) c_nm)) ->
    (forall cp_idx c_nm f_nm f_ty,
       C.ConstantPool.lookup (C.class_constantpool class) cp_idx = Some (C.cpe_fieldref c_nm f_nm f_ty) ->
       C.A.ConstantPoolAdditional.lookup (C.A.class_annot_constantpool (C.class_annotation class)) cp_idx = Some (C.A.cpae_instance_field) ->
       instance_field_ref_resolvable classes preclasses (C.class_name class) c_nm f_nm f_ty) ->
    subclass_assertions_satisfied classes class ->
    all_resolvable_for_class classes preclasses class.

Inductive all_resolvable_and_verified : R.cert_classpool -> R.Preclasspool.t -> Prop :=
| mk_all_resolvable_and_verified : forall classes preclasses,
    (forall c_nm c,
       R.Classpool.lookup (R.classpool classes) c_nm = Some c ->
       all_resolvable_for_class classes preclasses c /\ V.class_verified c) ->
    (forall c_nm pc,
       R.Preclasspool.lookup preclasses c_nm = Some pc ->
       all_resolvable_for_class classes preclasses (R.preclass_to_class pc) /\ V.class_verified (R.preclass_to_class pc)) ->
    all_resolvable_and_verified classes preclasses.

Definition fields_well_typed (classes:R.cert_classpool) (heap:E.ObjectHeap.t) : E.FieldStore.t -> Prop := fun statics =>
  forall c_nm f_nm ty v,
    E.FieldStore.lookup statics (c_nm, f_nm, ty) = Some v ->
    rt_ty_sat classes heap v (V.java_type_to_value_assertion ty).

Definition heap_well_typed (classes:R.cert_classpool) (heap:E.ObjectHeap.t) : Prop :=
   forall a nm fields,
    E.ObjectHeap.lookup heap a = Some (E.hp_object nm fields) ->
    (exists c, R.Classpool.lookup (R.classpool classes) nm = Some c /\ C.class_interface c = false /\ C.class_abstract c = false) /\
    fields_well_typed classes heap fields.

Inductive exception_classes : R.cert_classpool -> Prop :=
  mk_exception_classes : forall classes npe cce,
    R.Classpool.lookup (R.classpool classes) B.java_lang_NullPointerException = Some npe ->
    C.class_interface npe = false ->
    C.class_abstract npe = false ->
    R.Classpool.lookup (R.classpool classes) B.java_lang_ClassCastException = Some cce ->
    C.class_interface cce = false ->
    C.class_abstract cce = false ->
    R.sub_class classes B.java_lang_NullPointerException B.java_lang_Exception ->
    R.sub_class classes B.java_lang_ClassCastException B.java_lang_Exception ->
    R.sub_class classes B.java_lang_Exception B.java_lang_Throwable ->
    exception_classes classes.

Inductive safe_state : R.Preclasspool.t -> E.state -> option C.java_type -> Prop :=
  mk_safe_state : forall f fs classes preclasses heap current_ty final_ty static_fields,
    safe_current_frame classes heap f current_ty ->
    safe_frame_stack classes heap fs current_ty final_ty ->
    all_resolvable_and_verified classes preclasses ->
    fields_well_typed classes heap static_fields ->
    heap_well_typed classes heap ->
    exception_classes classes ->
    safe_state preclasses (E.mkState (f::fs) classes heap static_fields) final_ty.

Lemma preserve_exception_classes : forall classesA classesB,
  exception_classes classesA ->
  R.preserve_old_classes classesA classesB ->
  exception_classes classesB.
intros classesA classesB old_exc_classes preserve. 
destruct old_exc_classes as [classesA npe cce npe1 npe2 npe3 cce1 cce2 cce3 sub1 sub2 sub3].
eapply mk_exception_classes; eauto;
 eapply R.preserve_subclass; eauto.
Save.

Lemma preserve_fields_well_typed : forall classesA classesB heapA heapB statics,
  fields_well_typed classesA heapA statics ->
  R.preserve_old_classes classesA classesB ->
  preserve_heap_types heapA heapB ->
  fields_well_typed classesB heapB statics.
unfold fields_well_typed. intros. 
eapply preserve_rt_ty_sat; eauto.
Save.

Lemma preserve_heap_well_typed : forall classesA classesB heap,
  heap_well_typed classesA heap ->
  R.preserve_old_classes classesA classesB ->
  heap_well_typed classesB heap.
unfold heap_well_typed. intros. 
destruct (H _ _ _ H1).
split.
 destruct H2. exists x. intuition. 
 eapply preserve_fields_well_typed; eauto.
Save.

Lemma preserve_static_method_resolvable : forall classesA classesB preclasses caller c_nm m_nm m_desc,
  static_method_ref_resolvable classesA preclasses caller c_nm m_nm m_desc ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  static_method_ref_resolvable classesB preclasses caller c_nm m_nm m_desc.
intros. destruct H. 
destruct (R.preserve_resolve_method _ _ _ _ _ _ _ _ _ _ _ _ H2 H0 H1).
destruct H5. destruct H5. destruct H5.
apply (mk_static_method_ref_resolvable caller c_nm m_nm m_desc classesB preclasses x x0 x1 c m x2 code); assumption.
Save.

Lemma preserve_instance_special_method_resolvable : forall classesA classesB preclasses caller c_nm m_nm m_desc,
  instance_special_method_ref_resolvable classesA preclasses caller c_nm m_nm m_desc ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  instance_special_method_ref_resolvable classesB preclasses caller c_nm m_nm m_desc.
intros. destruct H. 
destruct (R.preserve_resolve_method _ _ _ _ _ _ _ _ _ _ _ _ H2 H0 H1).
destruct H6. destruct H6. destruct H6.
apply (mk_instance_special_method_ref_resolvable caller c_nm m_nm m_desc classesB preclasses x x0 x1 c m x2 code); assumption.
Save.

Lemma preserve_instance_method_resolvable : forall classesA classesB preclasses caller c_nm m_nm m_desc,
  instance_method_ref_resolvable classesA preclasses caller c_nm m_nm m_desc ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  instance_method_ref_resolvable classesB preclasses caller c_nm m_nm m_desc.
intros. destruct H. 
destruct (R.preserve_resolve_method _ _ _ _ _ _ _ _ _ _ _ _ H2 H0 H1).
destruct H4. destruct H4. destruct H4.
apply (mk_instance_method_ref_resolvable caller c_nm m_nm m_desc classesB preclasses x x0 x1 c m x2); assumption.
Save.

Lemma preserve_static_field_ref_resolvable : forall classesA classesB preclasses caller c_nm f_nm f_ty,
  static_field_ref_resolvable classesA preclasses caller c_nm f_nm f_ty ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  static_field_ref_resolvable classesB preclasses caller c_nm f_nm f_ty.
intros. destruct H. 
destruct (R.preserve_resolve_field _ _ _ _ _ _ _ _ _ _ _ _ H2 H0 H1).
destruct H4. destruct H4. destruct H4.
apply (mk_static_field_ref_resolvable caller c_nm f_nm f_ty classesB preclasses x x0 x1 c f x2); assumption.
Save.

Lemma preserve_instance_field_ref_resolvable : forall classesA classesB preclasses caller c_nm f_nm f_ty,
  instance_field_ref_resolvable classesA preclasses caller c_nm f_nm f_ty ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  instance_field_ref_resolvable classesB preclasses caller c_nm f_nm f_ty.
intros. destruct H. 
destruct (R.preserve_resolve_field _ _ _ _ _ _ _ _ _ _ _ _ H2 H0 H1).
destruct H5. destruct H5. destruct H5.
apply (mk_instance_field_ref_resolvable caller c_nm f_nm f_ty classesB preclasses x x0 x1 c f x2); assumption.
Save.

Lemma preserve_instantiatable_class_ref_resolvable : forall classesA classesB preclasses caller c_nm,
  instantiatable_class_ref_resolvable classesA preclasses caller c_nm ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  instantiatable_class_ref_resolvable classesB preclasses caller c_nm.
intros. destruct H. 
destruct (R.preserve_resolve_class _ _ _ _ _ _ _ _ _ _ H2 H0 H1).
 destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. 
apply (mk_instantiatable_class_ref_resolvable caller c_nm classesB preclasses x x0 x1 c x2 H5 H3 H4). 
Save.

Lemma preserve_class_ref_resolvable : forall classesA classesB preclasses caller c_nm,
  class_ref_resolvable classesA preclasses caller c_nm ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  class_ref_resolvable classesB preclasses caller c_nm.
intros classesA classesB preclasses caller c_nm resolveA presv only_add. 
destruct resolveA as [caller c_nm classes preclasses classesA' p o c H resolveA]. 
destruct (R.preserve_resolve_class _ _ _ _ _ _ _ _ _ _ resolveA presv only_add) as [classesB' [pB [oB [c_exB [resolveB X]]]]].
apply (mk_class_ref_resolvable caller c_nm classesB preclasses classesB' pB oB c c_exB resolveB). 
Save.

Lemma preserve_all_resolvable_for_class : forall classesA classesB preclasses class,
  all_resolvable_for_class classesA preclasses class ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  all_resolvable_for_class classesB preclasses class.
intros. destruct H. 
apply mk_all_resolvable_for_class; intros.
 eapply preserve_static_method_resolvable; eauto.
 eapply preserve_instance_special_method_resolvable; eauto.
 eapply preserve_instance_method_resolvable; eauto.
 eapply preserve_static_field_ref_resolvable; eauto.
 destruct (H5 _ _ H8). split. 
  eapply preserve_class_ref_resolvable; eauto.
  intros. eapply preserve_instantiatable_class_ref_resolvable; eauto.
 eapply preserve_instance_field_ref_resolvable; eauto.
 eapply preserve_subclass_assertions_satisfied; eauto.
Save. 

Lemma preserve_all_resolvable_and_verified : forall classesA classesB preclasses,
  all_resolvable_and_verified classesA preclasses ->
  R.preserve_old_classes classesA classesB ->
  R.only_add_from_preclasses classesA classesB preclasses ->
  all_resolvable_and_verified classesB preclasses.
intros. destruct H. 
apply mk_all_resolvable_and_verified; intros.
 (* classesB is ok: *)
 destruct (H1 _ _ H3).
  destruct H4. destruct H4. subst c. destruct (H2 _ _ H5). split; [eapply preserve_all_resolvable_for_class; eauto|idtac]; eauto. 
  destruct (H _ _ H4). split; [eapply preserve_all_resolvable_for_class|idtac]; eauto.
 (* preclasses are still ok *)
 destruct (H2 _ _ H3). split; [eapply preserve_all_resolvable_for_class|idtac]; eauto.
Save.


Lemma preserve_safe_frame_stack : forall classesA classesB heapA heapB fs ty1 ty2,
  safe_frame_stack classesA heapA fs ty1 ty2 ->
  R.preserve_old_classes classesA classesB ->
  preserve_heap_types heapA heapB ->
  safe_frame_stack classesB heapB fs ty1 ty2.
intros. induction H.
 constructor.
 eapply safe_stack_cons; eauto.
  eapply preserve_lvar_sat; eauto. 
  intros. apply H6; try assumption. 
   eapply R.preserve_old_classes_trans; eauto. 
   eapply preserve_heap_types_trans; eauto.
  unfold subclass_assertions_satisfied. intros. eapply R.preserve_subclass; eauto.
 eapply preserve_lvar_sat; eauto.
 eapply safe_stack_cons_void; eauto.
  eapply preserve_lvar_sat; eauto. 
  eapply preserve_stack_sat; eauto. 
  unfold subclass_assertions_satisfied. intros. eapply R.preserve_subclass; eauto.
 eapply preserve_lvar_sat; eauto.
Save.

Lemma static_method_ref_ok : forall classes preclasses nm class c_nm m_nm m_desc idx,
  all_resolvable_and_verified classes preclasses ->
  R.Classpool.lookup (R.classpool classes) nm = Some class ->
  V.C.ConstantPool.lookup (V.C.class_constantpool class) idx = Some (V.C.cpe_methodref c_nm m_nm m_desc) ->
  PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) idx = Some (PreV.VA.cpae_static_method) ->
  exists classes', exists p, exists o, exists c, exists m, exists H, exists code,
    E.R.resolve_method (E.R.C.class_name class) c_nm m_nm m_desc classes preclasses = E.R.load_ok _ (classes':=classes') p o (c,m) H
    /\ E.R.C.method_code m = Some code
    /\ E.R.C.method_static m = true
    /\ V.static_method_verified c m m_desc
    /\ all_resolvable_and_verified classes' preclasses
    /\ subclass_assertions_satisfied classes' c.
intros classes preclasses nm class0 c_nm m_nm m_desc idx all_randv nm_is_class0 cp_lookup cpa_lookup.
set (all_randv':=all_randv). generalize all_randv'. clear all_randv'. 
destruct 1 as [classes preclasses classes_ok _].
destruct (classes_ok _ _ nm_is_class0) as [class0_randv _].
destruct class0_randv as [classes preclasses class0 ref_ok _ _ _ _ _ _].
change V.C.cpe_methodref with C.cpe_methodref in cp_lookup.
pose (B:=ref_ok _ _ _ _ cp_lookup cpa_lookup). generalize B. 
change E.R.C.class_name with C.class_name.
destruct 1 as [caller c_nm m_nm m_desc classes preclasses classes' p o c m H code resolve_ok m_not_static m_not_abstract m_code].
assert (all_randv':all_resolvable_and_verified classes' preclasses). 
 eapply preserve_all_resolvable_and_verified; eauto. 
exists classes'. exists p. exists o. exists c. exists m. exists H. exists code. 
 intuition;
 destruct all_randv' as [classes' preclasses classes_verified _];
 clear resolve_ok;
 destruct H as [c_ok [m_ok _]];
 destruct (classes_verified _ _ c_ok) as [c_all_randv c_verified]; simpl in *.
  destruct c_verified. destruct (H _ _ _ m_ok). eauto.
  destruct c_all_randv. assumption.
Save.
Implicit Arguments static_method_ref_ok [classes preclasses nm c_nm m_nm m_desc idx].

Lemma instance_special_method_ref_ok : forall classes preclasses nm class c_nm m_nm m_desc idx,
  all_resolvable_and_verified classes preclasses ->
  R.Classpool.lookup (R.classpool classes) nm = Some class ->
  V.C.ConstantPool.lookup (V.C.class_constantpool class) idx = Some (V.C.cpe_methodref c_nm m_nm m_desc) ->
  PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) idx = Some (PreV.VA.cpae_instance_special_method) ->
  exists classes', exists p, exists o, exists c, exists m, exists H, exists code,
    E.R.resolve_method (E.R.C.class_name class) c_nm m_nm m_desc classes preclasses = E.R.load_ok _ (classes':=classes') p o (c,m) H
    /\ E.R.C.method_code m = Some code
    /\ E.R.C.method_static m = false
    /\ E.R.C.method_abstract m = false
    /\ V.instance_method_verified c m m_desc
    /\ all_resolvable_and_verified classes' preclasses
    /\ subclass_assertions_satisfied classes' c.
intros classes preclasses nm class0 c_nm m_nm m_desc idx all_randv nm_is_class0 cp_lookup cpa_lookup.
set (all_randv':=all_randv). generalize all_randv'. clear all_randv'. 
destruct 1 as [classes preclasses classes_ok _].
destruct (classes_ok _ _ nm_is_class0) as [class0_randv _].
destruct class0_randv as [classes preclasses class0 _ ref_ok _ _ _ _ _].
change V.C.cpe_methodref with C.cpe_methodref in cp_lookup.
pose (B:=ref_ok _ _ _ _ cp_lookup cpa_lookup). generalize B. 
change E.R.C.class_name with C.class_name.
destruct 1 as [caller c_nm m_nm m_desc classes preclasses classes' p o c m H code resolve_ok m_not_static m_not_abstract m_code].
assert (all_randv':all_resolvable_and_verified classes' preclasses). 
 eapply preserve_all_resolvable_and_verified; eauto. 
exists classes'. exists p. exists o. exists c. exists m. exists H. exists code. 
 intuition;
 destruct all_randv' as [classes' preclasses classes_verified _];
 clear resolve_ok;
 destruct H as [c_ok [m_ok _]];
 destruct (classes_verified _ _ c_ok) as [c_all_randv c_verified]; simpl in *.
  destruct c_verified. destruct (H _ _ _ m_ok). eauto.
  destruct c_all_randv. assumption.
Save.
Implicit Arguments instance_special_method_ref_ok [classes preclasses nm c_nm m_nm m_desc idx].

Lemma instance_method_ref_ok : forall classes preclasses nm class c_nm m_nm m_desc idx,
  all_resolvable_and_verified classes preclasses ->
  R.Classpool.lookup (R.classpool classes) nm = Some class ->
  V.C.ConstantPool.lookup (V.C.class_constantpool class) idx = Some (V.C.cpe_methodref c_nm m_nm m_desc) ->
  PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) idx = Some (PreV.VA.cpae_instance_method) ->
  exists classes', exists p, exists o, exists c, exists m, exists H,
    E.R.resolve_method (E.R.C.class_name class) c_nm m_nm m_desc classes preclasses = E.R.load_ok _ (classes':=classes') p o (c,m) H
    /\ E.R.C.method_static m = false
    /\ all_resolvable_and_verified classes' preclasses.
intros classes preclasses nm class0 c_nm m_nm m_desc idx all_randv nm_is_class0 cp_lookup cpa_lookup.
set (all_randv':=all_randv). generalize all_randv'. clear all_randv'. 
destruct 1 as [classes preclasses classes_ok _].
destruct (classes_ok _ _ nm_is_class0) as [class0_randv _].
destruct class0_randv as [classes preclasses class0 _ _ ref_ok _ _ _ _].
change V.C.cpe_methodref with C.cpe_methodref in cp_lookup.
pose (B:=ref_ok _ _ _ _ cp_lookup cpa_lookup). generalize B. 
change E.R.C.class_name with C.class_name.
destruct 1 as [caller c_nm m_nm m_desc classes preclasses classes' p o c m H code resolve_ok m_not_static m_not_abstract m_code].
assert (all_randv':all_resolvable_and_verified classes' preclasses). 
 eapply preserve_all_resolvable_and_verified; eauto. 
exists classes'. exists p. exists o. exists c. exists m. exists H.  
 intuition;
 destruct all_randv' as [classes' preclasses classes_verified _];
 clear resolve_ok;
 destruct H as [c_ok [m_ok _]];
 destruct (classes_verified _ _ c_ok) as [c_all_randv c_verified]; simpl in *.
Save.
Implicit Arguments instance_method_ref_ok [classes preclasses nm c_nm m_nm m_desc idx].

Lemma static_field_ref_ok : forall classes preclasses nm class c_nm f_nm f_ty idx,
  all_resolvable_and_verified classes preclasses ->
  R.Classpool.lookup (R.classpool classes) nm = Some class ->
  V.C.ConstantPool.lookup (V.C.class_constantpool class) idx = Some (V.C.cpe_fieldref c_nm f_nm f_ty) ->
  PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) idx = Some (PreV.VA.cpae_static_field) ->
  exists classes', exists p, exists o, exists c, exists f, exists H,
    E.R.resolve_field (E.R.C.class_name class) c_nm f_nm f_ty classes preclasses = E.R.load_ok _ (classes':=classes') p o (c,f) H
    /\ E.R.C.field_static f = true
    /\ all_resolvable_and_verified classes' preclasses.
intros classes preclasses nm class0 c_nm m_nm m_desc idx all_randv nm_is_class0 cp_lookup cpa_lookup.
set (all_randv':=all_randv). generalize all_randv'. clear all_randv'. 
destruct 1 as [classes preclasses classes_ok _].
destruct (classes_ok _ _ nm_is_class0) as [class0_randv _].
destruct class0_randv as [classes preclasses class0 _ _ _ ref_ok _ _ _].
change V.C.cpe_fieldref with C.cpe_fieldref in cp_lookup.
pose (B:=ref_ok _ _ _ _ cp_lookup cpa_lookup). generalize B. 
change E.R.C.class_name with C.class_name.
destruct 1 as [caller c_nm m_nm m_desc classes preclasses classes' p o c m H code resolve_ok m_not_static m_not_abstract m_code].
assert (all_randv':all_resolvable_and_verified classes' preclasses). 
 eapply preserve_all_resolvable_and_verified; eauto. 
exists classes'. exists p. exists o. exists c. exists m. exists H.  
 intuition;
 destruct all_randv' as [classes' preclasses classes_verified _];
 clear resolve_ok;
 destruct H as [c_ok [m_ok _]];
 destruct (classes_verified _ _ c_ok) as [c_all_randv c_verified]; simpl in *.
Save.
Implicit Arguments static_field_ref_ok [classes preclasses nm c_nm f_nm f_ty idx].

Lemma instance_field_ref_ok : forall classes preclasses nm class c_nm f_nm f_ty idx,
  all_resolvable_and_verified classes preclasses ->
  R.Classpool.lookup (R.classpool classes) nm = Some class ->
  V.C.ConstantPool.lookup (V.C.class_constantpool class) idx = Some (V.C.cpe_fieldref c_nm f_nm f_ty) ->
  PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) idx = Some (PreV.VA.cpae_instance_field) ->
  exists classes', exists p, exists o, exists c, exists f, exists H,
    E.R.resolve_field (E.R.C.class_name class) c_nm f_nm f_ty classes preclasses = E.R.load_ok _ (classes':=classes') p o (c,f) H
    /\ E.R.C.field_static f = false
    /\ E.R.C.field_final f = false
    /\ all_resolvable_and_verified classes' preclasses.
intros classes preclasses nm class0 c_nm m_nm m_desc idx all_randv nm_is_class0 cp_lookup cpa_lookup.
set (all_randv':=all_randv). generalize all_randv'. clear all_randv'. 
destruct 1 as [classes preclasses classes_ok _].
destruct (classes_ok _ _ nm_is_class0) as [class0_randv _].
destruct class0_randv as [classes preclasses class0 _ _ _ _ _ ref_ok _].
change V.C.cpe_fieldref with C.cpe_fieldref in cp_lookup.
pose (B:=ref_ok _ _ _ _ cp_lookup cpa_lookup). generalize B. 
change E.R.C.class_name with C.class_name.
destruct 1 as [caller c_nm m_nm m_desc classes preclasses classes' p o c m H code resolve_ok m_not_static m_not_abstract m_code].
assert (all_randv':all_resolvable_and_verified classes' preclasses). 
 eapply preserve_all_resolvable_and_verified; eauto. 
exists classes'. exists p. exists o. exists c. exists m. exists H.  
 intuition;
 destruct all_randv' as [classes' preclasses classes_verified _];
 clear resolve_ok;
 destruct H as [c_ok [m_ok _]];
 destruct (classes_verified _ _ c_ok) as [c_all_randv c_verified]; simpl in *.
Save.
Implicit Arguments instance_field_ref_ok [classes preclasses nm c_nm f_nm f_ty idx].

Lemma instantiatable_class_ref_ok : forall classes preclasses nm class c_nm idx,
  all_resolvable_and_verified classes preclasses ->
  R.Classpool.lookup (R.classpool classes) nm = Some class ->
  V.C.ConstantPool.lookup (V.C.class_constantpool class) idx = Some (V.C.cpe_classref c_nm) ->
  PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) idx = Some (PreV.VA.cpae_instantiable_class) ->
  exists classes', exists p, exists o, exists c, exists H,
    E.R.resolve_class (E.R.C.class_name class) c_nm classes preclasses = E.R.load_ok _ (classes':=classes') p o c H
    /\ E.R.C.class_interface c = false
    /\ E.R.C.class_abstract c = false
    /\ all_resolvable_and_verified classes' preclasses.
intros classes preclasses nm class0 c_nm idx all_randv nm_is_class0 cp_lookup cpa_lookup.
set (all_randv':=all_randv). generalize all_randv'. clear all_randv'. 
destruct 1 as [classes preclasses classes_ok _].
destruct (classes_ok _ _ nm_is_class0) as [class0_randv _].
destruct class0_randv as [classes preclasses class0 _ _ _ _ ref_ok _ _].
change V.C.cpe_classref with C.cpe_classref in cp_lookup.
destruct (ref_ok _ _ cp_lookup) as [_ ref_ok']. pose (B:=ref_ok' cpa_lookup). generalize B. 
change E.R.C.class_name with C.class_name.
destruct 1 as [caller c_nm classes preclasses classes' p o c H resolve_ok c_not_interface c_not_abstract].
assert (all_randv':all_resolvable_and_verified classes' preclasses). 
 eapply preserve_all_resolvable_and_verified; eauto. 
exists classes'. exists p. exists o. exists c. exists H.  
 intuition;
 destruct all_randv' as [classes' preclasses classes_verified _];
 clear resolve_ok;
 destruct H as [c_ok [m_ok _]];
 destruct (classes_verified _ _ c_ok) as [c_all_randv c_verified]; simpl in *.
Save.
Implicit Arguments instantiatable_class_ref_ok [classes preclasses nm c_nm idx].

Lemma class_ref_ok : forall classes preclasses nm class c_nm idx,
  all_resolvable_and_verified classes preclasses ->
  R.Classpool.lookup (R.classpool classes) nm = Some class ->
  V.C.ConstantPool.lookup (V.C.class_constantpool class) idx = Some (V.C.cpe_classref c_nm) ->
  exists classes', exists p, exists o, exists c, exists H,
    E.R.resolve_class (E.R.C.class_name class) c_nm classes preclasses = E.R.load_ok _ (classes':=classes') p o c H
    /\ all_resolvable_and_verified classes' preclasses.
intros classes preclasses nm class0 c_nm idx all_randv nm_is_class0_classes cp_lookup.
set (all_randv':=all_randv). generalize all_randv'. clear all_randv'. intro. 
destruct all_randv' as [classes preclasses classes_ok _].
destruct (classes_ok _ _ nm_is_class0_classes) as [class0_randv _].
destruct class0_randv as [classes preclasses class0 _ _ _ _ classref_ok _ _].
change V.C.ConstantPool.lookup with C.ConstantPool.lookup in cp_lookup.
change V.C.class_constantpool with C.class_constantpool in cp_lookup.
change V.C.cpe_classref with C.cpe_classref in cp_lookup.
destruct (classref_ok _ _ cp_lookup) as [classref_ok2 _].
change E.R.C.class_name with C.class_name.
destruct classref_ok2 as [caller c_nm classes preclasses classes' p o c c_nm_is_c resolve_ok]. 
assert (all_randv':all_resolvable_and_verified classes' preclasses). 
 eapply preserve_all_resolvable_and_verified; eauto. 
exists classes'. exists p. exists o. exists c. exists c_nm_is_c. intuition.
Save.
Implicit Arguments class_ref_ok [classes preclasses nm c_nm idx].

Lemma fields_well_typed_update : forall classes heap statics c f t v,
  fields_well_typed classes heap statics ->
  rt_ty_sat classes heap v (V.java_type_to_value_assertion t) ->
  fields_well_typed classes heap (E.FieldStore.update statics (c,f,t) v).
unfold fields_well_typed. intros.
destruct (E.FullFieldDesc.eq_dec (c,f,t) (c_nm, f_nm, ty)).
 inversion e. subst. rewrite E.FieldStore.lookup_update in H1. inversion H1. subst. assumption.
 rewrite E.FieldStore.indep_lookup in H1. apply (H _ _ _ _ H1). assumption. 
Save.

Lemma fields_empty_always_well_typed : forall classes heap,
  fields_well_typed classes heap E.FieldStore.empty.
unfold fields_well_typed. intros. 
rewrite E.FieldStore.lookup_empty in H. discriminate.
Save.

Hint Resolve preserve_safe_frame_stack preserve_lvar_sat preserve_stack_sat preserve_subclass_assertions_satisfied
             preserve_fields_well_typed preserve_heap_well_typed R.preserve_subclass preserve_exception_classes
             R.preserve_old_classes_id.

Lemma get_null_pointer_exception : forall classes,
  exception_classes classes ->
  exists npe,
    R.Classpool.lookup (R.classpool classes) E.R.B.java_lang_NullPointerException = Some npe /\
    E.R.C.class_interface npe = false /\
    E.R.C.class_abstract npe = false /\
    R.sub_class classes E.R.B.java_lang_NullPointerException E.R.B.java_lang_Throwable /\
    R.sub_class classes E.R.B.java_lang_NullPointerException E.R.B.java_lang_Exception.
intros. destruct H as [classes npe cce npe1 npe2 npe3 _ _ _ sub1 _ sub3].
exists npe. intuition. eapply R.sub_class_trans; eauto.
Save.

Lemma get_class_cast_exception : forall classes,
  exception_classes classes ->
  exists cce,
    R.Classpool.lookup (R.classpool classes) E.R.B.java_lang_ClassCastException = Some cce /\
    E.R.C.class_interface cce = false /\
    E.R.C.class_abstract cce = false /\
    R.sub_class classes E.R.B.java_lang_ClassCastException E.R.B.java_lang_Throwable /\
    R.sub_class classes E.R.B.java_lang_ClassCastException E.R.B.java_lang_Exception.
intros. destruct H as [classes npe cce _ _ _ cce1 cce2 cce3 _ sub2 sub3].
exists cce. intuition. eapply R.sub_class_trans; eauto.
Save.

Lemma object_creation_props : forall heap t heap' a classes c,
  R.Classpool.lookup (R.classpool classes) t = Some c ->
  C.class_interface c = false ->
  C.class_abstract c = false ->
  E.ObjectHeap.new heap (E.hp_object t E.FieldStore.empty) = (heap', a) ->
  heap_well_typed classes heap ->
     preserve_heap_types heap heap'
  /\ rt_ty_sat classes heap' (E.rt_addr (Some a)) (C.A.va_addr t)
  /\ heap_well_typed classes heap'
  /\ E.ObjectHeap.lookup heap' a = Some (E.hp_object t E.FieldStore.empty).
intros. unfold E.ObjectHeap.new in H2.
destruct heap. inversion H2. clear H2. 
assert (preserve_heap_types (E.ObjectHeap.mkHeap max_addr actual_heap max_unallocated) heap').
 subst. unfold preserve_heap_types. unfold E.ObjectHeap.lookup. simpl. intros.
 destruct (E.ObjectHeap.Key.eq_dec a a0).
  subst. rewrite (max_unallocated a0) in H2.
   discriminate.
   omega.
  rewrite E.ObjectHeap.S.indep_lookup. 
   exists fields. assumption.
   assumption.
subst. split.
 assumption.
 split.
  eapply ty_sat_addr2. 
   unfold E.ObjectHeap.lookup. simpl. apply E.ObjectHeap.S.lookup_update.
   apply R.sub_class_refl.
  split.
   unfold heap_well_typed in *. unfold E.ObjectHeap.lookup in *. simpl in *. intros. 
   destruct (E.ObjectHeap.Key.eq_dec a a0). 
    subst. rewrite E.ObjectHeap.S.lookup_update in H4. inversion H4. subst. split.
     exists c. auto.
     apply fields_empty_always_well_typed.
    rewrite E.ObjectHeap.S.indep_lookup in H4. destruct (H3 _ _ _ H4). eauto.
     assumption.       
   unfold E.ObjectHeap.lookup. simpl. apply E.ObjectHeap.S.lookup_update.
Save.
Implicit Arguments object_creation_props [heap heap' a].

Lemma heap_update_props : forall heap x ty f1 f2 nm fields a classes,
  E.ObjectHeap.lookup heap a = Some (E.hp_object nm fields) ->
  heap_well_typed classes heap ->
  rt_ty_sat classes heap x (V.java_type_to_value_assertion ty) ->
    exists heap', E.ObjectHeap.update heap a (E.hp_object nm (E.FieldStore.update fields (f1,f2,ty) x)) = Some heap'
                  /\ heap_well_typed classes heap'
                  /\ preserve_heap_types heap heap'.
intros. unfold E.ObjectHeap.update. destruct heap.
destruct (E.ObjectHeap.lookup_informative_Prop actual_heap a).
 match goal with |- ex (fun _ => Some ?v = Some _ /\ heap_well_typed _ _ /\ preserve_heap_types ?h _) => exists v; assert (preserve_heap_types h v) end. 
  unfold preserve_heap_types. unfold E.ObjectHeap.lookup in *. simpl in *. intros. 
  destruct (E.ObjectHeap.Key.eq_dec a a0).
   subst. rewrite E.ObjectHeap.S.lookup_update. rewrite H2 in H. inversion H. 
    exists (E.FieldStore.update fields (f1, f2, ty) x). reflexivity.
   rewrite E.ObjectHeap.S.indep_lookup. 
    exists fields0. assumption.
    assumption.
 split. 
  reflexivity.
  split. 
   unfold heap_well_typed. unfold E.ObjectHeap.lookup. simpl. intros. 
   destruct (E.ObjectHeap.Key.eq_dec a a0).
    subst. rewrite E.ObjectHeap.S.lookup_update in H3. inversion H3. subst. 
    destruct (H0 _ _ _ H). split.
     assumption.
     eapply fields_well_typed_update; eauto. eapply preserve_rt_ty_sat; eauto.
    rewrite E.ObjectHeap.S.indep_lookup in H3. 
     destruct (H0 _ _ _ H3). split.
      assumption.
      eapply preserve_fields_well_typed; eauto.
     assumption.
   assumption.
 unfold E.ObjectHeap.lookup in H. simpl in H. rewrite e in H. discriminate.
Save.
Implicit Arguments heap_update_props [heap x ty f1 f2 nm fields a].

Lemma sub_class_exists : forall classes Anm Bnm Bc,
  R.Classpool.lookup (R.classpool classes) Bnm = Some Bc ->
  R.sub_class classes Anm Bnm ->
  exists Ac, R.Classpool.lookup (R.classpool classes) Anm = Some Ac.
intros. inversion H0.
 subst. exists Bc. assumption.
 exists c. assumption.
Save.

Lemma sub_class_has_super_class : forall classes Anm Bnm Ac,
  R.Classpool.lookup (R.classpool classes) Anm = Some Ac ->
  R.sub_class classes Anm Bnm ->
  Anm = Bnm \/ exists nm, C.class_super_class Ac = Some nm /\ R.sub_class classes nm Bnm.
intros classes Anm Bnm Ac A_exists A_isa_B. inversion A_isa_B. 
 left. reflexivity.
 right. rewrite A_exists in H. inversion H. subst. exists s_nm. split; assumption.
Save.

Lemma all_randv_implies_instance_method_verified : forall classes preclasses B_nm Bc d Bm,
  R.Classpool.lookup (R.classpool classes) B_nm = Some Bc ->
  C.MethodList.lookup (C.class_methods Bc) d = Some Bm ->
  C.method_static Bm = false ->
  all_resolvable_and_verified classes preclasses ->
  V.instance_method_verified Bc Bm (snd d).
intros classes preclasses B_nm Bc d Bm B_exists Bm_exists Bm_not_static all_randv.
destruct all_randv as [classes preclasses all_r_and_v _].
destruct (all_r_and_v _ _ B_exists) as [_ B_verified].
destruct B_verified as [Bc B_verified]. destruct d as [m_nm m_d]. destruct (B_verified _ _ _ Bm_exists) as [_ Bm_verified]. 
auto. 
Save.

Lemma lookup_virtual_method_aux_props : forall classes oA_nm scc preclasses B_nm Bc d Bm A_nm,
  R.Classpool.lookup (R.classpool classes) B_nm = Some Bc ->
  C.MethodList.lookup (C.class_methods Bc) d = Some Bm ->
  C.method_static Bm = false ->
  oA_nm = Some A_nm ->
  R.sub_class classes A_nm B_nm ->
  all_resolvable_and_verified classes preclasses ->
   exists Cc, exists Cm,
   E.lookup_virtual_method_aux classes oA_nm d scc = inl _ (Cc, Cm)
   /\ R.Classpool.lookup (R.classpool classes) (C.class_name Cc) = Some Cc
   /\ C.method_static Cm = false
   /\ C.MethodList.lookup (C.class_methods Cc) d = Some Cm
   /\ R.sub_class classes A_nm (C.class_name Cc)
   /\ V.instance_method_verified Cc Cm (snd d).
intros classes oA_nm scc. elim scc using R.super_class_chain_ind2.

intros preclasses B_nm Bc d Bm A_nm B_exists Bm_exists Bm_not_static contr.
discriminate.

intros nm Ac A_exists s IH. 
intros preclasses B_nm Bc d Bm A_nm B_exists Bm_exists Bm_not_static nm_eq A_isa_B all_r_and_v.
simpl. 
inversion nm_eq. subst. clear nm_eq.
destruct (sub_class_has_super_class classes A_nm B_nm Ac A_exists A_isa_B) as [AB_eq | [Ac_super [Ac_super_eq Ac_super_isa_B]]].
 (* This class is actually B *)
 change (R.Classpool.lookup (R.classpool classes)) with (E.R.Classpool.lookup (E.R.classpool classes)) in B_exists.
 subst. destruct (E.R.Classpool.lookup_informative (E.R.classpool classes) B_nm) as [[Bc' B_exists'] | noB].
  (* B exists, as we knew already *)
  rewrite B_exists' in B_exists. inversion B_exists. subst. clear B_exists.
  change (C.MethodList.lookup (C.class_methods Bc)) with (E.R.C.MethodList.lookup (E.R.C.class_methods Bc)) in Bm_exists.
  rewrite Bm_exists. 
  change (E.R.C.method_static) with (C.method_static).
  rewrite Bm_not_static. 
  exists Bc. exists Bm. intuition.
   eapply R.cert_classpool_names. apply B_exists'.
   change C.class_name with R.C.class_name. rewrite (R.cert_classpool_names_2 B_exists'). constructor.
   eapply all_randv_implies_instance_method_verified; eauto.
  (* B doesn't exist! this is unpossible *)
  rewrite noB in B_exists. discriminate.
 (* This class must have a super class *)
 change R.Classpool.lookup with E.R.Classpool.lookup in A_exists.
 change R.classpool with E.R.classpool in A_exists.
 destruct (E.R.Classpool.lookup_informative (E.R.classpool classes) A_nm) as [[Ac' A_exists'] | noA].
  (* The class exists, as we knew it would *)
  rewrite A_exists' in A_exists. inversion A_exists. subst. clear A_exists.
  destruct (option_dec (E.R.C.MethodList.lookup (E.R.C.class_methods Ac) d)) as [[Am Am_exists] | noAm].
   (* Method was found *)
   rewrite Am_exists. destruct (bool_dec (E.R.C.method_static Am)) as [Am_static | Am_not_static].
    (* but is static *)
    rewrite Am_static. 
    destruct (IH Ac (eq_ind_r (fun nm => E.R.Classpool.lookup (E.R.classpool classes) nm = Some Ac) A_exists' (refl_equal A_nm)) preclasses B_nm Bc d Bm Ac_super)
          as [Cc [Cm [lookup_succeeds [Cc_exists [Cm_not_static [Cm_exists [Ac_super_isa_C Cm_verified]]]]]]]; auto.
    exists Cc. exists Cm. intuition.
     eapply E.R.sub_class_step; eauto.
    (* is not static *)
    rewrite Am_not_static.
    exists Ac. exists Am. intuition.
     eapply E.R.cert_classpool_names. apply A_exists'.
     change C.class_name with R.C.class_name. rewrite (R.cert_classpool_names_2 A_exists'). constructor.
     eapply all_randv_implies_instance_method_verified; eauto.
   (* Method was not found *)
   rewrite noAm. 
   destruct (IH Ac (eq_ind_r (fun nm => E.R.Classpool.lookup (E.R.classpool classes) nm = Some Ac) A_exists' (refl_equal A_nm)) preclasses B_nm Bc d Bm Ac_super)
          as [Cc [Cm [lookup_succeeds [Cc_exists [Cm_not_static [Cm_exists [Ac_super_isa_C Cm_verified]]]]]]]; auto.
    exists Cc. exists Cm. intuition.
     eapply R.sub_class_step; eauto.
  (* The class does not exists: unpossible *)
  elimtype False. rewrite noA in A_exists. discriminate. 
Save.   

Lemma lookup_virtual_method_props : forall classes preclasses B_nm Bc d Bm A_nm Ac,
  R.Classpool.lookup (R.classpool classes) B_nm = Some Bc ->
  C.MethodList.lookup (C.class_methods Bc) d = Some Bm ->
  C.method_static Bm = false ->
  R.sub_class classes A_nm B_nm ->
  R.Classpool.lookup (R.classpool classes) A_nm = Some Ac ->
  C.class_interface Ac = false ->
  C.class_abstract Ac = false ->
  all_resolvable_and_verified classes preclasses ->
   exists Cc:E.R.C.class, exists Cm:E.R.C.method,
   E.lookup_virtual_method classes A_nm d = Some (inl _ (Cc,Cm))
   /\ R.Classpool.lookup (R.classpool classes) (C.class_name Cc) = Some Cc 
   /\ C.MethodList.lookup (C.class_methods Cc) d = Some Cm
   /\ R.sub_class classes A_nm (C.class_name Cc)
   /\ V.instance_method_verified Cc Cm (snd d). 
intros classes preclasses B_nm Bc d Bm A_nm Ac B_exists Bm_exists Bm_not_static A_isa_B A_exists A_not_interface A_not_abstract all_r_and_v. 
unfold E.lookup_virtual_method.
destruct (sub_class_has_super_class classes A_nm B_nm Ac A_exists A_isa_B) as [AB_eq | [Ac_super [Ac_super_eq Ac_super_isa_B]]].
 (* A is the same as B *)
 subst. rewrite B_exists in A_exists. inversion A_exists. subst. clear A_exists.
 change R.Classpool.lookup with E.R.Classpool.lookup in B_exists.
 change R.classpool with E.R.classpool in B_exists.
 destruct (E.R.Classpool.lookup_informative (E.R.classpool classes) B_nm) as [[Bc' B_exists'] | no_B].
  (* B exists, as we knew it would *)
  rewrite B_exists' in B_exists. inversion B_exists. subst. clear B_exists.
  destruct (bool_informative (E.R.C.class_interface Ac)) as [Ac_interface | Ac_not_interface'].
   (* Turns out that B was an interface. But this impossible! *)
   change E.R.C.class_interface with C.class_interface in Ac_interface. rewrite Ac_interface in A_not_interface. discriminate.
   (* B is a class *)
   change C.MethodList.lookup with E.R.C.MethodList.lookup in Bm_exists.
   change C.class_methods with E.R.C.class_methods in Bm_exists.
   rewrite Bm_exists. change E.R.C.method_static with C.method_static. rewrite Bm_not_static. 
   exists Ac. exists Bm. intuition.
     eapply R.cert_classpool_names. apply B_exists'.
     change C.class_name with R.C.class_name. rewrite (R.cert_classpool_names_2 B_exists'). constructor.
     eapply all_randv_implies_instance_method_verified; eauto.
  (* No B, but this is not possible *)
  rewrite no_B in B_exists. discriminate.
 (* A has a super class *)
 change R.Classpool.lookup with E.R.Classpool.lookup in A_exists.
 change R.classpool with E.R.classpool in A_exists.
 destruct (E.R.Classpool.lookup_informative (E.R.classpool classes) A_nm) as [[Ac' A_exists'] | Anm_not_exists].
  (* The class is there, which we knew already *)
  rewrite A_exists' in A_exists. inversion A_exists. subst Ac'. clear A_exists.
  destruct (bool_informative (E.R.C.class_interface Ac)) as [A_interface | A_not_interface' ].
   (* It is an interface, which is impossible *)
   change E.R.C.class_interface with C.class_interface in A_interface. rewrite A_interface in A_not_interface. discriminate.
   (* It is not an interface *)
   set (scc:=(E.R.cert_classpool_gives_scc A_exists' A_not_interface')).
   generalize scc. clear scc. intro.
   destruct (lookup_virtual_method_aux_props classes (C.class_super_class Ac) scc preclasses B_nm Bc d Bm Ac_super)
         as [Cc [Cm [lookup_succeeds [Cc_exists [Cm_not_static [Cm_exists [Ac_super_isa_C Cm_verified]]]]]]]; auto.
   destruct (option_dec (E.R.C.MethodList.lookup (E.R.C.class_methods Ac) d)) as [[Am Am_exists] | no_Am].
    (* Method was actually found in this class *)
    rewrite Am_exists. destruct (bool_dec (E.R.C.method_static Am)) as [Am_static | Am_not_static].
     (* but it was static *)
     rewrite Am_static. 
     exists Cc. exists Cm. intuition.
      change E.R.C.class_super_class with C.class_super_class. rewrite lookup_succeeds. reflexivity.
      eapply R.sub_class_step; eauto.
     (* not static *)
     rewrite Am_not_static. exists Ac. exists Am. intuition.
      eapply R.cert_classpool_names. apply A_exists'.
      change C.class_name with R.C.class_name. rewrite (R.cert_classpool_names_2 A_exists'). constructor.
      eapply all_randv_implies_instance_method_verified; eauto.
    (* Method not there *)
    rewrite no_Am. 
    exists Cc. exists Cm. intuition.
     change E.R.C.class_super_class with C.class_super_class. rewrite lookup_succeeds. reflexivity.
     eapply R.sub_class_step; eauto.
  (* Class not found: impossible *)
  rewrite Anm_not_exists in A_exists. discriminate.
Save.

Lemma well_typed_heap_has_class : forall classes heap a nm fields,
  heap_well_typed classes heap ->
  E.ObjectHeap.lookup heap a = Some (E.hp_object nm fields) ->
  exists c, R.Classpool.lookup (R.classpool classes) nm = Some c /\ C.class_interface c = false /\ C.class_abstract c = false.
intros classes heap a nm fields good_heap obj_exists. 
destruct (good_heap _ _ _ obj_exists) as [[c [c_exists [c_not_interface c_not_abstract]]] _].
exists c. auto.
Save.

Definition lift_prop_2 := fun (A B:Set) (p:A -> B -> Prop) (a:option A) (b:option B) =>
  match a,b with
  | Some a, Some b => p a b
  | None,   None   => True
  | _,_            => False
  end.
Implicit Arguments lift_prop_2 [A B].

Ltac normal_continue MS CS :=
  left; match goal with [_:E.cont ?st = _|- _ ] => exists st end;
  split; [try assumption
         |eapply mk_safe_state;
          [eapply mk_safe_current_frame;
           [ eauto (* class exists *)
           | apply MS
           | apply CS
           | eauto (* lvars ok *)
           | eauto (* stack ok *)
           | eauto (* subclasses ok *) ]
          |eauto (* frame stack *)
          |eauto (* all resovable and verified *)
          |eauto (* static fields well typed *)
          |eauto (* heap well typed *)
          |eauto (* exceptions exist *)]].

Lemma unwind_stack_ok : forall preclasses classes heap fs current_ty final_ty static_fields addr res c c_exists,
  safe_frame_stack classes heap fs current_ty final_ty ->
  all_resolvable_and_verified classes preclasses ->
  fields_well_typed classes heap static_fields ->
  heap_well_typed classes heap ->
  exception_classes classes ->
  rt_ty_sat classes heap (E.rt_addr (Some addr)) (C.A.va_addr (C.class_name c)) ->
  R.sub_class classes (C.class_name c) B.java_lang_Throwable ->
  R.sub_class classes (C.class_name c) B.java_lang_Exception -> 
  match E.unwind_stack classes fs addr c c_exists with
  | Some nil =>
     E.stop_exn (E.mkState nil classes heap static_fields) addr
  | Some fs =>
     E.cont (E.mkState fs classes heap static_fields)
  | None => E.wrong
  end = res ->
  (exists s', E.cont s' = res /\ safe_state preclasses s' final_ty) \/
  (exists s', exists v, E.stop s' v = res /\
                        lift_prop_2 (rt_ty_sat (E.state_classes s') (E.state_object_heap s')) v
                                    (option_map V.java_type_to_value_assertion final_ty)) \/
  (exists s', exists e, exists cnm, exists fields, E.stop_exn s' e = res /\ E.ObjectHeap.lookup (E.state_object_heap s') e = Some (E.hp_object cnm fields) /\ R.sub_class (E.state_classes s') cnm B.java_lang_Exception).
intros preclasses classes heap fs current_ty final_ty static_fields addr res c c_exists.
intros fs_safe all_randv statics_good heap_good exc_good addr_ok c_isa_throwable c_isa_exception E.
generalize current_ty fs_safe E. clear current_ty fs_safe E. induction fs; intros.
 (* empty frame stack *)
 simpl in *.
 inversion addr_ok. subst. right. right. 
 exists (E.mkState nil classes heap static_fields). exists addr. exists nm'. exists fields.
 intuition. eapply R.sub_class_trans; eauto. 
 (* frame stack contains stuff *)
 simpl in E. destruct a as [op_stack lvars pc code class].
 change E.R.C.code_exception_table with C.code_exception_table in E.
 inversion fs_safe;
  (* frame stack for returning something *)
  subst op_stack0 lvars0 pc0 code0 class0 fs0 current_ty final_ty0;
  (destruct (check_exception_handlers_prop _ heap _ _ _ _ _ _ c_exists _ _ H13 c_isa_exception H14 (refl_equal _))
        as [[pc' [l' [s' [search_handlers_ok [cert_lookup_ok [lvar_imp stack_will_be_ok]]]]]] | search_handlers_ok];
   [(* handler found *)
    rewrite <- search_handlers_ok in E;
    assert (lvars_ok:lvar_sat classes heap lvars l');
    [eapply lvar_assertion_implication_sound; eauto
    |normal_continue H7 cert_lookup_ok]
   (* handler not found *)
   |rewrite <- search_handlers_ok in E;
    eapply IHfs; eauto]).
Save.

Lemma stack_type_is_cat2_ok1 : forall classes heap v s,
  rt_ty_sat classes heap v (V.stack_type_to_value_assertion s) ->
  V.stack_type_is_cat2 s = true ->
  E.val_category v = C.category2.
intros. destruct s; inversion H; try discriminate; reflexivity.
Save.

Lemma stack_type_is_cat2_ok2 : forall classes heap v s,
  rt_ty_sat classes heap v (V.stack_type_to_value_assertion s) ->
  V.stack_type_is_cat2 s = false ->
  E.val_category v = C.category1.
intros. destruct s; inversion H; try discriminate; reflexivity.
Save.

Hint Resolve stack_type_is_cat2_ok1 stack_type_is_cat2_ok2.

Ltac throw_built_in E exc_nm get_exc preclasses classes heap preserve_classes exceptions_exist exc_check_ok subclass_satisfied' code_is_safe :=
  destruct (pair_dec (E.ObjectHeap.new heap (E.hp_object exc_nm E.FieldStore.empty)))
        as [heap' [addr new_result]];
  rewrite new_result in E;
  destruct (get_exc _ (preserve_exception_classes _ _ exceptions_exist preserve_classes))
        as [exc [exc_exists [exc_not_interface [exc_not_abstract [exc_isa_throwable exc_isa_exception]]]]];
  destruct (object_creation_props exc_nm classes exc exc_exists exc_not_interface exc_not_abstract new_result) as [preserve_heap_ty [alloced_ok [heap'_good heap'_lookup_ok]]]; eauto;
  rewrite heap'_lookup_ok in E;
  destruct (E.R.Classpool.lookup_informative (E.R.classpool classes) exc_nm) as [[c c_exists] | not_exists];
  [rewrite <- (E.R.cert_classpool_names_2 c_exists) in exc_isa_throwable;
   rewrite <- (E.R.cert_classpool_names_2 c_exists) in exc_isa_exception;
   rewrite <- (E.R.cert_classpool_names_2 c_exists) in alloced_ok;
   destruct (check_exception_handlers_prop _ heap' _ _ _ _ _ _ (E.R.cert_classpool_names c_exists) _ _ subclass_satisfied' exc_isa_exception exc_check_ok (refl_equal _))
         as [[pc' [l'' [s' [search_handlers_ok [cert_lookup_ok [lvar_imp stack_will_be_ok]]]]]] | search_handlers_ok];
   change V.C.code_exception_table with E.R.C.code_exception_table in search_handlers_ok;
   [(* The handler was here, no unwinding necessary *)
    rewrite <- search_handlers_ok in E; normal_continue code_is_safe cert_lookup_ok;
    eapply lvar_assertion_implication_sound;
     [apply subclass_satisfied'
     |eapply V.lvar_assertion_implication_trans; [idtac | apply lvar_imp ]
     |eapply preserve_lvar_sat; eauto]
   |(* Have to unwind the stack *)
    rewrite <- search_handlers_ok in E; eapply (unwind_stack_ok preclasses classes heap'); eauto; set (B:=1)]
  |change (E.R.Classpool.lookup (E.R.classpool classes)) with (R.Classpool.lookup (R.classpool classes)) in not_exists;
   rewrite not_exists in exc_exists; discriminate].

Lemma exec_safe : forall s rt res preclasses, safe_state preclasses s rt -> E.exec preclasses s = res ->
   (exists s', E.cont s' = res /\ safe_state preclasses s' rt) \/
   (exists s', exists v, E.stop s' v = res /\ lift_prop_2 (rt_ty_sat (E.state_classes s') (E.state_object_heap s')) v (option_map V.java_type_to_value_assertion rt)) \/
   (exists s', exists e, exists cnm, exists fields,
       E.stop_exn s' e = res /\
       E.ObjectHeap.lookup (E.state_object_heap s') e = Some (E.hp_object cnm fields) /\
       R.sub_class (E.state_classes s') cnm B.java_lang_Exception).
intros s rt res preclasses safety E.

destruct safety as [f fs classes preclasses heap current_ty final_ty static_fields
                    f_safe frame_stack_is_safe refs_good statics_good heap_good exceptions_exist].
destruct f_safe as [cert op_stack lvars pc class current_ty lvar_assertion stack_assertion code
                    class_exists code_is_safe cert_lookup_ok lvars_ok stack_ok subclassing_satisfied
                    no_exception_handlers].
inversion code_is_safe as [cert' cert_not_too_big instructions_safe]. subst cert'.
destruct (nth_error_ok _ (C.code_code code) _ (cert_not_too_big _ _ cert_lookup_ok)) as [opcode op_exists].
pose (B:=instructions_safe _ _ op_exists). generalize B. clear B. intro. 
destruct B as [cert pc op s1 s2 l1 l2 cert_lookup_ok' wp_code lvar_imp stack_imp]. 
change PreV.VA.Cert.lookup with C.A.Cert.lookup in cert_lookup_ok'.
rewrite cert_lookup_ok' in cert_lookup_ok. inversion cert_lookup_ok. subst lvar_assertion stack_assertion.
pose (good_lvars:=lvar_assertion_implication_sound _ _ _ subclassing_satisfied _ _ _ lvar_imp lvars_ok).
pose (good_stack:=stack_assertion_implication_sound _ _ _ subclassing_satisfied _ _ _ stack_imp stack_ok).
generalize good_lvars good_stack. 
clear cert_lookup_ok cert_lookup_ok' good_lvars good_stack lvar_imp stack_imp stack_ok lvars_ok l1 s1
      cert_not_too_big instructions_safe.
intros.

simpl in E. 
(*change C.code_code with E.C.code_code in op_exists.
rewrite op_exists in E.*)
change V.C.opcode with E.C.opcode in op.
replace (nth_error (E.C.code_code code) pc) with (Some op) in E.
destruct op; try discriminate; simpl in * |- *.

(* op_iarithb *)
destruct i; try discriminate;
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code; simpl in wp_code; destruct x;
destruct_opt (V.unpush class PreV.VA.va_int (l,s)) H0 wp_code; simpl in wp_code; destruct x;
destruct_opt (V.unpop PreV.VA.va_int (l0,s0)) H1 wp_code; destruct x;
destruct (sem_unpop good_stack wp_code); subst l2; destruct H3; destruct H2; destruct H2; destruct H3;
destruct (sem_unpop H4 H1); subst l1; destruct H6; destruct H5; destruct H5; destruct H6; subst x0;
destruct (sem_unpush subclassing_satisfied H7 H0); subst l;
destruct x; inversion H2; destruct x1; inversion H5; subst i i0;

rewrite H3 in E;
match goal with
[_:E.cont (E.mkState (E.mkFrame (E.rt_int ?v::_) _ _ _ _ :: _) _ _ _) = _ |- _] =>
  pose (H8 (E.rt_int v) (ty_sat_int classes heap v)) end;
normal_continue code_is_safe H.

(* op_iarithu *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code; simpl in wp_code; destruct x.
destruct_opt (V.unpush class PreV.VA.va_int (l,s)) H0 wp_code; destruct x.
destruct (sem_unpop good_stack wp_code); destruct H2; destruct H2; destruct H2; destruct H3. subst l2.
destruct (sem_unpush subclassing_satisfied H4 H0). subst l. 
destruct x; inversion H2. subst i0. 

rewrite H3 in E. destruct i. 
match goal with [_:E.cont (E.mkState (E.mkFrame (E.rt_int ?v::_) _ _ _ _ :: _) _ _ _) = _ |- _] => pose (H5 (E.rt_int v) (ty_sat_int classes heap v)) end;
normal_continue code_is_safe H. 

(* op_iinc *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code. simpl in wp_code.
destruct_opt (V.unstore class n x false) H0 wp_code. simpl in wp_code.
destruct x0. 
destruct (PreV.VA.value_assertion_eq_dec v PreV.VA.va_int); try discriminate.
subst v. simpl in wp_code. 
assert (not_top:PreV.VA.va_int <> PreV.VA.va_top). unfold not. intro. discriminate.
destruct a. destruct x.
destruct (sem_unretrieve subclassing_satisfied not_top good_lvars wp_code) as [tmp_eq [v [v_ok [lookup_ok l_ok]]]]. subst s2. 
destruct (sem_unstore l_ok H0) as [tmp_eq v_will_be_ok]. subst s0. 

rewrite lookup_ok in E. inversion v_ok. subst v. 
destruct (v_will_be_ok (E.rt_int (B.Int32.add i t))) as [lv' [update_ok lv'_ok]].
 constructor. 
 intros. discriminate.
 intros. reflexivity.
change B.Int32.add with E.B.Int32.add in update_ok.
rewrite update_ok in E. normal_continue code_is_safe H.

(* op_dup *)
destruct (option_dec (PreV.VA.Cert.lookup cert (S pc))) as [[a cert_ok]|IsNone]; [rewrite cert_ok in wp_code| rewrite IsNone in wp_code; discriminate].
simpl in wp_code.
destruct (option_dec (V.unpush_2 a)) as [[x1 unpush_ok1]|IsNone]; [rewrite unpush_ok1 in wp_code | rewrite IsNone in wp_code; discriminate ].
simpl in wp_code. destruct x1 as [v1 a1].
destruct (option_dec (V.unpush_2 a1)) as [[x2 unpush_ok2]|IsNone]; [rewrite unpush_ok2 in wp_code | rewrite IsNone in wp_code; discriminate ].
simpl in wp_code. destruct x2 as [v2 a2].
destruct (option_dec (V.value_assertion_merge class v1 v2)) as [[v merge_ok]|IsNone]; [rewrite merge_ok in wp_code | rewrite IsNone in wp_code; discriminate ].
simpl in wp_code. 
match goal with _:(if ?x then _ else _) = _ |- _ => change x with (V.value_assertion_implication_dec class v PreV.VA.va_cat1) in wp_code end.
destruct (bool_dec (V.value_assertion_implication_dec class v PreV.VA.va_cat1)) as [is_cat1|isnt_cat1]; [rewrite is_cat1 in wp_code|rewrite isnt_cat1 in wp_code; discriminate].
destruct a1 as [l0 s0]. destruct a2 as [l1 s1].
destruct a as [l s].

destruct (sem_unpop good_stack wp_code) as [lvar_eq [v0 [s' [v0_v_sat [op_stack_eq s'_good]]]]].
subst l2. 
destruct (sem_known_unpush s'_good unpush_ok2) as [lvar_eq pre_v0_s'_ok]. subst l1. 
assert (v0_s'_good:stack_sat classes heap (v0::s') s0).
 apply pre_v0_s'_ok. eapply value_assertion_implication_sound; eauto.
  eapply V.value_assertion_merge_p2. apply merge_ok. 
destruct (sem_known_unpush v0_s'_good unpush_ok1) as [lvar_eq pre_v0_v0_s'_good]. subst l0.
assert (v0_v0_s'_good:stack_sat classes heap (v0::v0::s') s).
 apply pre_v0_v0_s'_good. eapply value_assertion_implication_sound; eauto.
  eapply V.value_assertion_merge_p1. apply merge_ok. 

rewrite op_stack_eq in E.
rewrite (va_category1 classes heap) in E.
normal_continue code_is_safe cert_ok.
 eapply value_assertion_implication_sound; eauto; apply V.value_assertion_implication_dec_sound; assumption.

(* op_nop *)
normal_continue code_is_safe wp_code.

(* op_pop *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code. simpl in wp_code. destruct x.
destruct (sem_unpop good_stack wp_code). subst l2. destruct H1. destruct H0. destruct H0. destruct H1. 
rewrite H1 in E. rewrite (va_category1 _ _ _ H0) in E. 
normal_continue code_is_safe H. 

(* op_load *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code. simpl in wp_code. destruct x. 
destruct_opt (V.unpush_2 (l,s0)) H0 wp_code. destruct x. simpl in wp_code.
destruct_bool (V.value_assertion_implication_dec class v (V.stack_type_to_value_assertion s)) H1 wp_code. simpl in wp_code.
destruct a.
destruct (sem_unretrieve subclassing_satisfied (va_not_top class v s H1) good_lvars wp_code) as [tmp_eq [ v0 [v0_ok [lookup_ok l0_ok]]]]. subst s2.
destruct (sem_known_unpush good_stack H0) as [tmp_eq stack_will_be_ok]. 
subst l0. pose (stack_will_be_ok _ v0_ok).

rewrite lookup_ok in E. normal_continue code_is_safe H.

(* op_store *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code. simpl in wp_code. destruct x.
destruct_opt (V.unstore class n (l, s0) (V.stack_type_is_cat2 s)) H0 wp_code. destruct x. simpl in wp_code.
destruct_opt (V.value_assertion_merge class (V.stack_type_to_value_assertion s) v) H1 wp_code. simpl in wp_code.
destruct a.
destruct (sem_unpop good_stack wp_code) as [tmp_eq [v0 [s' [v0_ok [op_stack_form s'_ok]]]]]. subst l2.
destruct (sem_unstore good_lvars H0) as [tmp_eq v0_will_be_ok]. subst s1.
assert (v0_ok2:rt_ty_sat classes heap v0 v). 
 eapply value_assertion_implication_sound. 
  apply subclassing_satisfied.
  eapply V.value_assertion_merge_p2. apply H1.
  apply v0_ok.
assert (v0_ok3:rt_ty_sat classes heap v0 (V.stack_type_to_value_assertion s)). 
 eapply value_assertion_implication_sound. 
  apply subclassing_satisfied.
  eapply V.value_assertion_merge_p1. apply H1.
  apply v0_ok.
destruct (v0_will_be_ok v0 v0_ok2) as [lv' [update_ok lv'_ok]]; eauto.

rewrite op_stack_form in E. rewrite update_ok in E. normal_continue code_is_safe H.

(* op_instanceof *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code. simpl in wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code.
destruct x0; try discriminate.
simpl in wp_code.
destruct_opt (V.unpush class PreV.VA.va_int x) H1 wp_code. simpl in wp_code. 
destruct x. destruct x0.

destruct (sem_unpop good_stack wp_code) as [tmp_eq [v [s' [v_ok [op_stack_form s'_ok]]]]]. subst l2.
destruct (sem_unpush subclassing_satisfied s'_ok H1) as [tmp_eq stk_will_be_ok]. subst l0.
destruct (class_ref_ok _ refs_good class_exists H0) as [classes' [p [o [c [c_exists [resolve_c refs_good']]]]]].
pose (one_ok:=preserve_stack_sat _ _ _ _ _ _ (stk_will_be_ok _ (ty_sat_int classes heap B.Int32.one)) p (preserve_heap_types_id heap)).
pose (zero_ok:=preserve_stack_sat _ _ _ _ _ _ (stk_will_be_ok _ (ty_sat_int classes heap B.Int32.zero)) p (preserve_heap_types_id heap)).
rewrite op_stack_form in E. 
change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0.
change V.C.class_constantpool with E.R.C.class_constantpool in H0.
change V.C.cpe_classref with C.cpe_classref in H0.
rewrite H0 in E. 
rewrite resolve_c in E. 
inversion v_ok. 
 (* Reference exists *)
 subst v. rewrite H2 in E.
 destruct (heap_good a nm fields H2) as [[c' [c'_exists _]] _].
 pose (c'_exists2:=p _ _ c'_exists).
 destruct (E.R.Classpool.lookup_informative (E.R.classpool classes') nm). 
  destruct s1. destruct (E.R.check_subclass (E.R.cert_classpool_names e) (E.R.C.class_name c));
   normal_continue code_is_safe H.
  rewrite c'_exists2 in e. discriminate.
 (* Reference is null *)
 subst v. normal_continue code_is_safe H.

(* op_invokespecial *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code; simpl in wp_code.
destruct (option_dec (V.check_exception_handlers code class cert pc (V.C.code_exception_table code))) as [[exc_l exc_check_ok] | exc_check_fail]; [rewrite exc_check_ok in wp_code|rewrite exc_check_fail in wp_code; discriminate].
simpl in wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; 
destruct x0; try discriminate; simpl in wp_code;
destruct_opt (PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) t) H1 wp_code;
destruct x0; try discriminate; simpl in wp_code.

destruct_opt (V.C.descriptor_ret_type d) H2 wp_code; destruct x as [l s];
 [destruct_opt (V.unpush class (V.java_type_to_value_assertion x0) (l,s)) H3 wp_code;
    simpl in wp_code; destruct x; rename H3 into unpush_1; rename x0 into ret_ty
 |simpl in wp_code; rename l into l0];
(destruct (option_dec (V.lvar_assertion_merge class l0 exc_l)) as [[l' merge_ok] | merge_fail]; [rewrite merge_ok in wp_code; simpl in wp_code|rewrite merge_fail in wp_code;discriminate]);
inversion wp_code; subst s2 l2; clear wp_code;
destruct (sem_pop_n good_stack); destruct H3; destruct H3; destruct H4;
inversion H5; subst x0 t2 a; clear H5;
[destruct (sem_unpush_2 subclassing_satisfied H10 unpush_1); rename H6 into ret_val_ok; subst l | idtac];
rewrite rev_length in H3; rewrite map_length in H3;

destruct (instance_special_method_ref_ok _ refs_good class_exists H0 H1);
destruct H5; destruct H5; destruct H5; destruct H5; destruct H5; destruct H5; destruct H5; destruct H6; destruct H7; destruct H8; destruct H11; destruct H12;
destruct H11;
change V.C.method_code with E.R.C.method_code in H14;
rewrite H6 in H14; inversion H14; subst x6;
change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0;
change V.C.class_constantpool with E.R.C.class_constantpool in H0;
change V.C.cpe_methodref with E.R.C.cpe_methodref in H0; rewrite H0 in E;
rewrite H5 in E;
generalize E; clear E; dependent inversion x5; intros;
[replace (E.pop_n (length (E.R.C.descriptor_arg_types md)) op_stack) with (Some (x, v::s1)) in E
|replace (E.pop_n (length (E.R.C.descriptor_arg_types md)) op_stack) with (Some (x, v::s0)) in E];

(assert (subclass_satisfied':subclass_assertions_satisfied x0 class);
[eauto
|change PreV.VA.va_addr with C.A.va_addr in H9;
 (inversion H9;
  (* The reference was null *)
  [subst v x3;
   throw_built_in E E.R.B.java_lang_NullPointerException get_null_pointer_exception preclasses x0 heap x1 exceptions_exist exc_check_ok subclass_satisfied' code_is_safe;
   eapply V.lvar_assertion_merge_p2; apply merge_ok
  (* The reference was not null *)
  |subst t0 v;
  rewrite H7 in E; rewrite H8 in E; rewrite H6 in E;
  assert (stk_ok:stack_sat_exact x0 heap (E.rt_addr (Some a0)::(rev x)) (map V.java_type_to_value_assertion (V.C.ty_ref (V.C.class_name class0)::V.C.descriptor_arg_types md)));
  [simpl; apply stk_sat_exact_cons;
   [destruct a; simpl in H23; eapply ty_sat_addr2; 
    [apply H21 
    |eapply R.sub_class_trans;
     [eapply R.preserve_subclass; eauto
     |eauto]]
   |eapply preserve_stack_sat_exact;
     [apply stack_sat_exact_rev_2; apply H4
     |assumption
     |apply preserve_heap_types_id]]
  |destruct (sem_argument_prep subclass_satisfied' H17 stk_ok) as [new_l TMP];
   destruct TMP as [stack_to_lvars_ok new_l_ok];
   match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ =>
     change v with (E.stack_to_lvars (E.rt_addr (Some a0)::rev x) (V.C.code_max_lvars code0)) in E end;
   rewrite stack_to_lvars_ok in E;
   left; match goal with [_:E.cont ?st = _ |- _ ] => exists st end;
   split;
   [assumption
   |eapply mk_safe_state;
    [eapply mk_safe_current_frame;
     [assumption
     |apply H15
     |apply H16
     |eapply lvar_assertion_implication_sound; [apply H13 | apply H18 | apply new_l_ok ]
     |eapply stack_assertion_implication_sound; [apply H13 | apply H19 | constructor ]
     |assumption]
    |idtac
    |assumption
    |eauto|eauto|eauto]]]])]).

rewrite H2. eapply safe_stack_cons; simpl; eauto. 
 eapply lvar_assertion_implication_sound. 
  eauto.
  eapply V.lvar_assertion_merge_p1; eauto. eapply preserve_lvar_sat; eauto. 
 intros. apply ret_val_ok.
  eapply R.preserve_old_classes_trans; eauto.
  eapply preserve_heap_types_trans; eauto.
  assumption.
 eapply lvar_assertion_implication_sound. 
  eauto.
  eapply V.lvar_assertion_merge_p2; eauto. eapply preserve_lvar_sat; eauto. 

rewrite H2. eapply safe_stack_cons_void; eauto.
 eapply lvar_assertion_implication_sound. 
  eauto.
  eapply V.lvar_assertion_merge_p1; eauto. eapply preserve_lvar_sat; eauto. 
 eapply lvar_assertion_implication_sound. 
  eauto.
  eapply V.lvar_assertion_merge_p2; eauto. eapply preserve_lvar_sat; eauto. 

(* op_invokestatic *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code; simpl in wp_code. 
destruct (option_dec (V.check_exception_handlers code class cert pc (V.C.code_exception_table code))) as [[exc_l exc_check_ok] | exc_check_fail]; [rewrite exc_check_ok in wp_code|rewrite exc_check_fail in wp_code; discriminate].
simpl in wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; 
destruct x0; try discriminate; simpl in wp_code;
destruct_opt (PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) t) H1 wp_code;
destruct x0; try discriminate; simpl in wp_code.

destruct_opt (V.C.descriptor_ret_type d) H2 wp_code; destruct x as [l s];
[destruct_opt (V.unpush class (V.java_type_to_value_assertion x0) (l,s)) H3 wp_code;
    simpl in wp_code; destruct x; rename H3 into unpush_1; rename x0 into ret_ty
|simpl in wp_code; rename l into l0];
(destruct (option_dec (V.lvar_assertion_merge class l0 exc_l)) as [[l' merge_ok] | merge_fail]; [rewrite merge_ok in wp_code; simpl in wp_code|rewrite merge_fail in wp_code;discriminate]);
inversion wp_code; subst s2 l2; clear wp_code;
destruct (sem_pop_n good_stack); destruct H3; destruct H3; destruct H4;
[destruct (sem_unpush_2 subclassing_satisfied H5 unpush_1); rename H7 into ret_val_ok; subst l | idtac];
rewrite rev_length in H3; rewrite map_length in H3;

destruct (static_method_ref_ok _ refs_good class_exists H0 H1);
destruct H6; destruct H6; destruct H6; destruct H6; destruct H6; destruct H6; destruct H6; destruct H7; destruct H8; destruct H9; destruct H10;
destruct H9;
change V.C.method_code with E.R.C.method_code in H9;
rewrite H7 in H9; inversion H9; subst x7;
destruct (sem_argument_prep (s:=rev x) subclassing_satisfied H14 (stack_sat_exact_rev_2 _ _ _ _ H4));
destruct H17;
change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0;
change V.C.class_constantpool with E.R.C.class_constantpool in H0;
change V.C.cpe_methodref with E.R.C.cpe_methodref in H0;
rewrite H0 in E;
replace (E.pop_n (length (E.R.C.descriptor_arg_types md)) op_stack) with (Some (x, x0)) in E;
rewrite H6 in E;
generalize E; clear E; dependent inversion x6; intros; 
rewrite H8 in E; rewrite H7 in E;
change E.R.C.code_max_lvars with V.C.code_max_lvars in E;
rewrite H17 in E;

(normal_continue H12 H13;
 [eapply lvar_assertion_implication_sound; eauto; eapply preserve_lvar_sat; eauto
 |eapply stack_assertion_implication_sound; eauto; constructor
 |idtac]).

rewrite H2; eapply safe_stack_cons; simpl; eauto. 
 eapply lvar_assertion_implication_sound. 
  eapply preserve_subclass_assertions_satisfied. apply subclassing_satisfied. assumption.
  eapply V.lvar_assertion_merge_p1; eauto. eapply preserve_lvar_sat; eauto. 
 intros. apply ret_val_ok.
  eapply R.preserve_old_classes_trans; eauto.
  eapply preserve_heap_types_trans; eauto.
  assumption.
 eapply lvar_assertion_implication_sound. 
  eapply preserve_subclass_assertions_satisfied. apply subclassing_satisfied. assumption.
  eapply V.lvar_assertion_merge_p2; eauto. eapply preserve_lvar_sat; eauto. 

rewrite H2; eapply safe_stack_cons_void; simpl; eauto. 
 eapply lvar_assertion_implication_sound. 
  eapply preserve_subclass_assertions_satisfied. apply subclassing_satisfied. assumption.
  eapply V.lvar_assertion_merge_p1; eauto. eapply preserve_lvar_sat; eauto. 
 eapply lvar_assertion_implication_sound. 
  eapply preserve_subclass_assertions_satisfied. apply subclassing_satisfied. assumption.
  eapply V.lvar_assertion_merge_p2; eauto. eapply preserve_lvar_sat; eauto. 

(* op_invokevirtual *)
(*destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code; simpl in wp_code.
destruct (option_dec (V.check_exception_handlers code class cert pc (V.C.code_exception_table code))) as [[exc_l exc_check_ok] | exc_check_fail]; [rewrite exc_check_ok in wp_code|rewrite exc_check_fail in wp_code; discriminate].
simpl in wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; 
destruct x0; try discriminate; simpl in wp_code;
destruct_opt (PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) t) H1 wp_code;
destruct x0; try discriminate; simpl in wp_code.

destruct_opt (V.C.descriptor_ret_type d) H2 wp_code; destruct x as [l s];
 [destruct_opt (V.unpush class (V.java_type_to_value_assertion x0) (l,s)) H3 wp_code;
    simpl in wp_code; destruct x; rename H3 into unpush_1; rename x0 into ret_ty
 |simpl in wp_code; rename l into l0];
(destruct (option_dec (V.lvar_assertion_merge class l0 exc_l)) as [[l' merge_ok] | merge_fail]; [rewrite merge_ok in wp_code; simpl in wp_code|rewrite merge_fail in wp_code;discriminate]);
inversion wp_code; subst s2 l2; clear wp_code;
destruct (sem_pop_n good_stack); destruct H3; destruct H3; destruct H4;
inversion H5; subst x0 t2 a; clear H5;
[destruct (sem_unpush_2 subclassing_satisfied H10 unpush_1); rename H6 into ret_val_ok; subst l | idtac];
rewrite rev_length in H3; rewrite map_length in H3;
destruct (instance_method_ref_ok _ refs_good class_exists H0 H1)
      as [classes' [p_classes_classes' [o_classes_classes' [cl [m [Hresolve [resolve_succeeds [m_static all_resolvable_classes']]]]]]]];
change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0;
change V.C.class_constantpool with E.R.C.class_constantpool in H0;
change V.C.cpe_methodref with E.R.C.cpe_methodref in H0;
rewrite H0 in E; rewrite resolve_succeeds in E.
(*generalize E; clear E; dependent inversion Hresolve as [cl_exists [m_exists t0_sc_cl]]; intro;*)
rewrite m_static in E;
[ replace (E.pop_n (length (E.R.C.descriptor_arg_types d)) op_stack) with (Some (x, v::s1)) in E
(*| replace (E.pop_n (length (E.R.C.descriptor_arg_types d)) op_stack) with (Some (x, v::s0)) in E*)
];
change PreV.VA.va_addr with C.A.va_addr in H9;

(assert (subclass_satisfied_in_classes':subclass_assertions_satisfied classes' class);
[eauto
| inversion H9;
  (* The reference was null *)
 [subst v x0;
  generalize E; clear E; dependent inversion Hresolve as [cl_exists [m_exists t0_sc_cl]]; intro;
  throw_built_in E E.R.B.java_lang_NullPointerException get_null_pointer_exception preclasses classes' heap p_classes_classes' exceptions_exist exc_check_ok subclass_satisfied_in_classes' code_is_safe;
  eapply V.lvar_assertion_merge_p2; apply merge_ok
  (* The reference was not null *)
 |subst v t0;
  rewrite H6 in E; idtac ]]).
  destruct (well_typed_heap_has_class _ _ _ _ _ heap_good H6) as [nm'_c [nm'_exists [nm'_not_interface nm'_not_abstract]]].
  destruct (lookup_virtual_method_props classes' preclasses (V.C.class_name cl) cl (t1, d) m nm' nm'_c)
        as [real_c [real_m [lookup_succeeded [real_c_exists [real_m_exists [nm'_isa_real_c real_m_verified]]]]]].
   clear E resolve_succeeds. destruct Hresolve as [cl_exists [m_exists t0_sc_cl]]. apply cl_exists.
   clear E resolve_succeeds. destruct Hresolve as [cl_exists [m_exists t0_sc_cl]]. apply m_exists.
   apply m_static.
   clear E resolve_succeeds. destruct Hresolve as [cl_exists [m_exists t0_sc_cl]]. eapply R.sub_class_trans; [eapply R.preserve_subclass; [apply H8|assumption]|assumption].
   apply (p_classes_classes' _ _ nm'_exists).
   apply nm'_not_interface.
   apply nm'_not_abstract.
   apply all_resolvable_classes'.
  change V.C.B.Methodname.t with E.B.Methodname.t in t1.
  change V.C.descriptor with E.R.C.descriptor in d.
  replace (E.lookup_virtual_method classes' nm' (t1,d)) with (Some (inl E.R.exn (pair real_c real_m))) in E.
rewrite lookup_succeeded in E.


  clear resolve_succeeds Hresolve;
  ; idtac ]]).
  (*assert (R.sub_class classes' nm' (V.C.class_name cl)).*)
  destruct (lookup_virtual_method_props classes' preclasses (V.C.class_name cl) cl (t1, d) m nm' nm'_c)
        as [real_c [real_m [lookup_succeeded [real_c_exists [real_m_exists [nm'_isa_real_c real_m_verified]]]]]].
  replace (E.lookup_virtual_method classes' nm' (t1,d)) with (Some (inl E.R.exn (real_c, real_m))) in E.
  set (B:=E.lookup_virtual_method classes' nm' (t1,d)) in *.

Check E.


  match goal with [ _:(match ?x with Some _ => ?a | None => ?b end = res) |- _ ] => idtac end.
    replace x with (Some (inl E.R.exn (real_c, real_m))) in E end.

rewrite lookup_succeeded in E.
  simpl in real_m_verified;
  destruct real_m_verified
        as [real_m real_c md real_m_cert real_m_l real_m_s real_m_code real_m_l'
            real_m_not_abstract real_m_has_code real_m_safe real_m_cert_lookup real_m_args real_m_lvar_imp real_m_stk_imp].
   change V.C.method with E.R.C.method in real_m.
   change V.C.class with E.R.C.class in real_c.
   change V.C.descriptor with E.C.descriptor in md.
   change V.C.B.Methodname.t with E.B.Methodname.t in t1.
   replace (E.lookup_virtual_method classes' nm' (t1,md)) with (Some (inl E.R.exn (real_c : E.R.C.class, real_m : E.R.C.method))) in E.
   rewrite lookup_succeeded in E.
  
rewrite lookup_succeeded in E.


   idtac]]]).
   change V.C.method with E.R.C.method in real_m.
   change V.C.class with E.R.C.class in real_c.
   change V.C.descriptor with E.C.descriptor in md.
   change V.C.B.Methodname.t with E.B.Methodname.t in t1.
   replace (E.lookup_virtual_method classes' nm' (t1,md)) with (Some (inl E.R.exn (real_c : E.R.C.class, real_m : E.R.C.method))) in E.
   rewrite lookup_succeeded in E.
   rewrite real_m_not_abstract in E;
   rewrite real_m_has_code in E;
   assert (stk_ok:stack_sat_exact classes' heap (E.rt_addr (Some a)::(rev x)) (map V.java_type_to_value_assertion (V.C.ty_ref (V.C.class_name real_c)::V.C.descriptor_arg_types md)));
   [simpl; apply stk_sat_exact_cons;
    [eapply ty_sat_addr2; [ apply H6 | assumption ]
    |eapply preserve_stack_sat_exact;
      [apply stack_sat_exact_rev_2; apply H4
      |assumption
      |apply preserve_heap_types_id]]
   |assert (subclass_satisfied':subclass_assertions_satisfied classes' real_c);
    [destruct all_resolvable_classes' as [classes' preclasses all_randv _];
     destruct (all_randv _ _ real_c_exists) as [real_c_randv _];
     destruct real_c_randv as [classes' preclasses real_c _ _ _ _ _ _ ss];
     assumption
    |destruct (sem_argument_prep subclass_satisfied' real_m_args stk_ok) as [new_l [stack_to_lvars_ok new_l_ok]];
     match goal with _:match ?v with Some _ => _ | None => _ end = _ |- _ =>
       change v with (E.stack_to_lvars (E.rt_addr (Some a)::rev x) (E.R.C.code_max_lvars real_m_code)) in E end;
     rewrite stack_to_lvars_ok in E;
     normal_continue real_m_safe real_m_cert_lookup;
     [eapply lvar_assertion_implication_sound; [eapply preserve_subclass_assertions_satisfied; eauto | apply real_m_lvar_imp | apply new_l_ok ]
     |eapply stack_assertion_implication_sound; [eapply preserve_subclass_assertions_satisfied; eauto | apply real_m_stk_imp | constructor ]
     |idtac]]]]]]).

rewrite H2. eapply safe_stack_cons; simpl; eauto. 
 eapply lvar_assertion_implication_sound. 
  eapply preserve_subclass_assertions_satisfied. apply subclassing_satisfied. assumption.
  eapply V.lvar_assertion_merge_p1; eauto. eapply preserve_lvar_sat; eauto. 
 intros. apply ret_val_ok.
  eapply V.E.R.preserve_old_classes_trans; eauto.
  eapply preserve_heap_types_trans; eauto.
  assumption.
 eapply lvar_assertion_implication_sound. 
  eapply preserve_subclass_assertions_satisfied. apply subclassing_satisfied. assumption.
  eapply V.lvar_assertion_merge_p2; eauto. eapply preserve_lvar_sat; eauto. 

rewrite H2. eapply safe_stack_cons_void; eauto.
 eapply lvar_assertion_implication_sound. 
  eapply preserve_subclass_assertions_satisfied. apply subclassing_satisfied. assumption.
  eapply V.lvar_assertion_merge_p1; eauto. eapply preserve_lvar_sat; eauto. 
 eapply lvar_assertion_implication_sound. 
  eapply preserve_subclass_assertions_satisfied. apply subclassing_satisfied. assumption.
  eapply V.lvar_assertion_merge_p2; eauto. eapply preserve_lvar_sat; eauto. *)

(* op_aconst_null *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code. destruct x. 
destruct (sem_unpush subclassing_satisfied good_stack wp_code). subst l2.
pose (H1 (E.rt_addr None) (ty_sat_null _ _)). 
normal_continue code_is_safe H.

(* op_checkcast *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code.
destruct (option_dec (V.check_exception_handlers code class cert pc (V.C.code_exception_table code))) as [[exc_l exc_check_ok] | exc_check_fail]; [rewrite exc_check_ok in wp_code|rewrite exc_check_fail in wp_code; discriminate].
simpl in wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; simpl in wp_code.
destruct x0; try discriminate.
destruct_opt (V.unpush class (PreV.VA.va_addr t0) x) H1 wp_code. simpl in wp_code.
destruct x0. destruct x.
destruct_opt (V.unpop PreV.VA.va_ref (l, s)) H2 wp_code. destruct x as [l1 s1]. simpl in wp_code.
destruct_opt (V.lvar_assertion_merge class l1 exc_l) H3 wp_code. 
inversion wp_code. subst x s1. clear wp_code.

destruct (sem_unpop good_stack H2) as [tmp_eq [v [s' [v_ok [op_stack_form s'_ok]]]]]. subst l1.
destruct (sem_unpush_2 subclassing_satisfied s'_ok H1) as [tmp_eq stack_will_be_ok]. subst l0.
destruct (class_ref_ok _ refs_good class_exists H0) as [classes' [p [o [c [c_exists [resolve_c refs_good']]]]]].

rewrite op_stack_form in E. 
change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0.
change V.C.class_constantpool with E.R.C.class_constantpool in H0.
change V.C.cpe_classref with E.R.C.cpe_classref in H0.
rewrite H0 in E. rewrite resolve_c in E. 
inversion v_ok. 
 (* Reference was not null *)
 subst v. rewrite H4 in E. 
 destruct (heap_good a nm fields H4) as [[c' [c'_exists _]] _].
 pose (c'_exists':=p _ _ c'_exists).
 destruct (E.R.Classpool.lookup_informative (E.R.classpool classes') nm) as [[c'2 c'_exists'2] | c'_not_exists ]. 
  destruct_bool (E.R.check_subclass (E.R.cert_classpool_names c'_exists'2) (E.R.C.class_name c)) H5 E.
   (* assignability check passed *)
   rewrite (E.R.cert_classpool_names_2 c_exists) in H5.
   normal_continue code_is_safe H.
    eapply lvar_assertion_implication_sound. eauto.
     eapply V.lvar_assertion_merge_p1. apply H3. eapply preserve_lvar_sat; eauto. 
    apply stack_will_be_ok; auto. eapply ty_sat_addr2. 
     apply H4.
     rewrite <- (E.R.cert_classpool_names_2 c'_exists'2). 
     apply (E.R.check_subclass_sound _ _ t0 (E.R.cert_classpool_names c'_exists'2)). apply H5. 
   (* assignability check failed: throw ClassCastException *)
   clear c c_exists resolve_c H5.
   clear s' s'_ok stack_will_be_ok op_stack_form.
   throw_built_in E E.R.B.java_lang_ClassCastException get_class_cast_exception preclasses classes' heap p exceptions_exist exc_check_ok (preserve_subclass_assertions_satisfied _ _ _ subclassing_satisfied p) code_is_safe.
   eapply V.lvar_assertion_merge_p2; apply H3.
  rewrite c'_exists' in c'_not_exists. discriminate.
 (* Reference was null *)
 subst v. assert (stack_ok:stack_sat classes' heap (E.rt_addr None::s') s0).
  apply stack_will_be_ok; auto. eapply ty_sat_addr1.
 normal_continue code_is_safe H; eauto.
  eapply lvar_assertion_implication_sound. eauto.
   eapply V.lvar_assertion_merge_p1. apply H3. eapply preserve_lvar_sat; eauto. 
 
(* op_getfield *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code.
destruct (option_dec (V.check_exception_handlers code class cert pc (V.C.code_exception_table code))) as [[exc_l exc_check_ok] | exc_check_fail]; [rewrite exc_check_ok in wp_code|rewrite exc_check_fail in wp_code; discriminate].
simpl in wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; simpl in wp_code;
destruct x0; try discriminate;
destruct_opt (PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) t) H1 wp_code;
destruct x0; try discriminate; simpl in wp_code.
destruct_opt (V.unpush class (V.java_type_to_value_assertion j) x) H2 wp_code. simpl in wp_code.
destruct x0. destruct x.
destruct_opt (V.unpop (PreV.VA.va_addr t0) (l, s)) H3 wp_code. destruct x as [l1 s1]. simpl in wp_code.
destruct_opt (V.lvar_assertion_merge class l1 exc_l) H4 wp_code. 
inversion wp_code. subst x s1. clear wp_code.

destruct (sem_unpop good_stack H3) as [tmp_eq [v [s' [v_ok [op_stack_form s'_ok]]]]]. subst l1.
destruct (sem_unpush subclassing_satisfied s'_ok H2)as [tmp_eq stack_will_be_ok]. subst l0.
destruct (instance_field_ref_ok _ refs_good class_exists H0 H1)
      as [classes' [p [o [class2 [f [resolve_H [resolve_ok [f_not_static [f_not_final all_randv]]]]]]]]].

rewrite op_stack_form in E. 
change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0.
change V.C.class_constantpool with E.R.C.class_constantpool in H0.
change V.C.cpe_fieldref with E.R.C.cpe_fieldref in H0.
rewrite H0 in E. rewrite resolve_ok in E. 
generalize E. clear E. dependent inversion resolve_H as [c2_exists f_exists]. intro.
rewrite f_not_static in E.
change PreV.VA.va_addr with C.A.va_addr in v_ok.
inversion v_ok. 
 (* reference is null *)
 subst x v. 
 clear s' s'_ok stack_will_be_ok op_stack_form. 
 throw_built_in E E.R.B.java_lang_NullPointerException get_null_pointer_exception preclasses classes' heap p exceptions_exist exc_check_ok (preserve_subclass_assertions_satisfied _ _ _ subclassing_satisfied p) code_is_safe.
 eapply V.lvar_assertion_merge_p2; apply H4.
 (* reference is non null *)
 subst v t0. rewrite H6 in E.
 change V.C.java_type with E.R.C.java_type in j.
 destruct_opt (E.FieldStore.lookup fields (E.R.C.class_name class2, E.R.C.field_name f, j)) H5 E.
  destruct (heap_good _ _ _ H6). pose (H9 _ _ _ _ H5). normal_continue code_is_safe H; eauto.
   eapply lvar_assertion_implication_sound. eauto.
   eapply V.lvar_assertion_merge_p1. apply H4. eapply preserve_lvar_sat; eauto. 
  pose (stack_will_be_ok _ (default_value_sat _ _ j)). normal_continue code_is_safe H; eauto.
   eapply lvar_assertion_implication_sound. eauto.
    eapply V.lvar_assertion_merge_p1. apply H4. eapply preserve_lvar_sat; eauto. 

(* op_getstatic *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; simpl in wp_code;
destruct x0; try discriminate;
destruct_opt (PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) t) H1 wp_code;
destruct x0; try discriminate; simpl in wp_code.

destruct (static_field_ref_ok _ refs_good class_exists H0 H1).
destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3.
destruct x.
destruct (sem_unpush subclassing_satisfied good_stack wp_code). subst l2.

change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0.
change V.C.class_constantpool with E.R.C.class_constantpool in H0.
change V.C.cpe_fieldref with E.R.C.cpe_fieldref in H0.
rewrite H0 in E. rewrite H2 in E. 
generalize E. clear E. dependent inversion x5. intro.
rewrite H3 in E. 
change V.C.java_type with E.R.C.java_type in j.
destruct_opt (E.FieldStore.lookup static_fields (E.R.C.class_name x3, E.R.C.field_name x4, j)) H5 E.
 pose (H6 _ (statics_good _ _ _ _ H5)). normal_continue code_is_safe H; eauto.
 pose (H6 _ (default_value_sat _ _ j)). normal_continue code_is_safe H; eauto.

(* op_new *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; simpl in wp_code;
destruct x0; try discriminate;
destruct_opt (PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) t) H1 wp_code;
destruct x0; try discriminate; simpl in wp_code.

destruct (instantiatable_class_ref_ok _ refs_good class_exists H0 H1).
destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. 
destruct x.
destruct (sem_unpush_2 subclassing_satisfied good_stack wp_code). subst l2.

change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0. 
change V.C.class_constantpool with E.R.C.class_constantpool in H0.
change V.C.cpe_classref with E.R.C.cpe_classref in H0.
rewrite H0 in E. rewrite H2 in E. rewrite H4 in E. rewrite H3 in E. 
destruct (pair_dec (E.ObjectHeap.new heap (E.hp_object t0 E.FieldStore.empty))) as [heap' [addr new_eq]].
rewrite new_eq in E. 
destruct (object_creation_props t0 x0 _ x4 H3 H4 new_eq) as [p_heap [a_ok [heap'_ok a_exists]]]. eauto. 
normal_continue code_is_safe H; eauto.

(* op_putfield *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code.
destruct (option_dec (V.check_exception_handlers code class cert pc (V.C.code_exception_table code))) as [[exc_l exc_check_ok] | exc_check_fail]; [rewrite exc_check_ok in wp_code|rewrite exc_check_fail in wp_code; discriminate].
simpl in wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; simpl in wp_code;
destruct x0; try discriminate;
destruct_opt (PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) t) H1 wp_code;
destruct x0; try discriminate; simpl in wp_code.
destruct_opt (V.unpop (PreV.VA.va_addr t0) x) H2 wp_code. simpl in wp_code.
destruct x. destruct x0.
destruct_opt (V.unpop (V.java_type_to_value_assertion j) (l0, s0)) H3 wp_code. destruct x as [l1 s1].
simpl in wp_code.
destruct_opt (V.lvar_assertion_merge class l1 exc_l) H4 wp_code. 
inversion wp_code. subst x s1. clear wp_code.

destruct (sem_unpop good_stack H3) as [tmp_eq [v [s' [v_ok [op_stack_form s'_ok]]]]]. subst l1.
destruct (sem_unpop s'_ok H2) as [tmp_eq [v' [s'0 [v'_ok [s'_form s'0_ok]]]]]. subst l0.  
destruct (instance_field_ref_ok _ refs_good class_exists H0 H1)
      as [classes' [p [o [class2 [f [resolve_H [resolve_ok [f_not_static [f_not_final all_randv]]]]]]]]].

rewrite op_stack_form in E. rewrite s'_form in E. 
change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0.
change V.C.class_constantpool with E.R.C.class_constantpool in H0.
change V.C.cpe_fieldref with E.R.C.cpe_fieldref in H0.
rewrite H0 in E. rewrite resolve_ok in E.
generalize E. clear E. dependent inversion resolve_H as [class2_exists f_exists]. intro.
rewrite f_not_static in E. rewrite f_not_final in E. simpl in E.
change PreV.VA.va_addr with C.A.va_addr in v'_ok.
inversion v'_ok. 
 (* reference is null *)
 subst v' x. 
 clear s' s'_ok op_stack_form s'_form.
 throw_built_in E E.R.B.java_lang_NullPointerException get_null_pointer_exception preclasses classes' heap p exceptions_exist exc_check_ok (preserve_subclass_assertions_satisfied _ _ _ subclassing_satisfied p) code_is_safe.
 eapply V.lvar_assertion_merge_p2; apply H4.
 (* reference is non null *)
 subst v' t0. rewrite H6 in E. 
 destruct (heap_update_props (x:=v) (ty:=j) (f1:=(E.R.C.class_name class2)) (f2:=(E.R.C.field_name f)) classes' H6)
       as [heap' [update_ok [heap'_ok preserve_heap]]]; eauto.
  eapply preserve_rt_ty_sat; eauto.
 change V.C.java_type with E.R.C.java_type in j.
 replace (E.ObjectHeap.update heap a (E.hp_object nm' (E.FieldStore.update fields (E.R.C.class_name class2, E.R.C.field_name f, j) v)))
    with (Some heap') in E.
 normal_continue code_is_safe H; eauto.
  eapply lvar_assertion_implication_sound. eauto.
   eapply V.lvar_assertion_merge_p1. apply H4. eapply preserve_lvar_sat; eauto. 

(* op_putstatic *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code.
destruct_opt (V.C.ConstantPool.lookup (V.C.class_constantpool class) t) H0 wp_code; simpl in wp_code;
destruct x0; try discriminate;
destruct_opt (PreV.VA.ConstantPoolAdditional.lookup (PreV.VA.class_annot_constantpool (V.C.class_annotation class)) t) H1 wp_code;
destruct x0; try discriminate; simpl in wp_code.
destruct (static_field_ref_ok _ refs_good class_exists H0 H1)
 as [classes' [p [o [c [f [H' [resolve_ok [f_static all_randv']]]]]]]].
destruct x.
destruct (sem_unpop good_stack wp_code) as [l_eq [v [s' [v_ok [s'_form s'_ok]]]]]. 
subst l2.

rewrite s'_form in E. 
change V.C.ConstantPool.lookup with E.R.C.ConstantPool.lookup in H0.
change V.C.class_constantpool with E.R.C.class_constantpool in H0.
change V.C.cpe_fieldref with E.R.C.cpe_fieldref in H0.
rewrite H0 in E. rewrite resolve_ok in E. 
generalize E. clear E. dependent inversion H'. intro.
rewrite f_static in E. normal_continue code_is_safe H; eauto.
 apply fields_well_typed_update; eauto.
  eapply preserve_rt_ty_sat; eauto.

(* op_if_acmp *)
destruct_opt (V.C.pc_plus_offset pc z) H wp_code. 
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H0 wp_code. simpl in wp_code.
destruct_opt (PreV.VA.Cert.lookup cert x) H1 wp_code. simpl in wp_code.
destruct_opt (V.assertion_merge class x0 x1) H2 wp_code. simpl in wp_code.
destruct_opt (V.unpop PreV.VA.va_ref x2) H3 wp_code. simpl in wp_code.
destruct x0. destruct x1. destruct x2. destruct x3. simpl in H2. 
destruct_opt (V.lvar_assertion_merge class l l0) H4 H2. simpl in H2.
destruct_opt (V.stack_assertion_merge class s s0) H5 H2. simpl in H2.
inversion H2. subst x0 x1. clear H2.
destruct (sem_unpop good_stack wp_code). subst l2. destruct H6. destruct H2. destruct H2. destruct H6.
destruct (sem_unpop H7 H3). subst l3. destruct H9. destruct H8. destruct H8. destruct H9. subst x1.
destruct x0; inversion H2; subst o;
destruct x2; inversion H8; subst o;
change V.C.pc_plus_offset with E.C.pc_plus_offset in H;

rewrite H6 in E;
destruct a;
(match goal with [_:match (if ?t then _ else _) with Some _ => _ | None => _ end = res |- _] => destruct t end;
[rewrite H in E; normal_continue code_is_safe H1;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p2; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p2; eauto | eauto ]]
|normal_continue code_is_safe H0;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p1; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p1; eauto | eauto ]]]).

(* op_if_icmp *)
destruct_opt (V.C.pc_plus_offset pc z) H wp_code. 
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H0 wp_code. simpl in wp_code.
destruct_opt (PreV.VA.Cert.lookup cert x) H1 wp_code. simpl in wp_code.
destruct_opt (V.assertion_merge class x0 x1) H2 wp_code. simpl in wp_code.
destruct_opt (V.unpop PreV.VA.va_int x2) H3 wp_code. simpl in wp_code.
destruct x0. destruct x1. destruct x2. destruct x3. simpl in H2. 
destruct_opt (V.lvar_assertion_merge class l l0) H4 H2. simpl in H2.
destruct_opt (V.stack_assertion_merge class s s0) H5 H2. simpl in H2.
inversion H2. subst x0 x1. clear H2.
destruct (sem_unpop good_stack wp_code). subst l2. destruct H6. destruct H2. destruct H2. destruct H6.
destruct (sem_unpop H7 H3). subst l3. destruct H9. destruct H8. destruct H8. destruct H9. subst x1.
destruct x0; inversion H2. subst i.
destruct x2; inversion H8. subst i.
change V.C.pc_plus_offset with E.C.pc_plus_offset in H.

rewrite H6 in E. 
destruct c;
(match goal with [_:match (if ?t then _ else _) with Some _ => _ | None => _ end = res |- _] => destruct t end;
[rewrite H in E; normal_continue code_is_safe H1;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p2; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p2; eauto | eauto ]]
|normal_continue code_is_safe H0;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p1; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p1; eauto | eauto ]]]).

(* op_if *)
destruct_opt (V.C.pc_plus_offset pc z) H wp_code. 
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H0 wp_code. simpl in wp_code.
destruct_opt (PreV.VA.Cert.lookup cert x) H1 wp_code. simpl in wp_code.
destruct_opt (V.assertion_merge class x0 x1) H2 wp_code. simpl in wp_code.
destruct x0. destruct x1. destruct x2. simpl in H2.
destruct_opt (V.lvar_assertion_merge class l l0) H3 H2. simpl in H2.
destruct_opt (V.stack_assertion_merge class s s0) H4 H2. simpl in H2.
inversion H2. subst x0 x1. clear H2.
destruct (sem_unpop good_stack wp_code). subst l1. destruct H5. destruct H2. destruct H2. destruct H5.
destruct x0; inversion H2. subst i.
change V.C.pc_plus_offset with E.C.pc_plus_offset in H.

rewrite H5 in E.
destruct c;
(match goal with [_:match (if ?t then _ else _) with Some _ => _ | None => _ end = res |- _ ] => destruct t end;
[rewrite H in E; normal_continue code_is_safe H1;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p2; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p2; eauto | eauto ]]
|normal_continue code_is_safe H0;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p1; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p1; eauto | eauto ]]]).

(* op_ifnonnull *)
destruct_opt (V.C.pc_plus_offset pc z) H wp_code. 
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H0 wp_code. simpl in wp_code.
destruct_opt (PreV.VA.Cert.lookup cert x) H1 wp_code. simpl in wp_code.
destruct_opt (V.assertion_merge class x0 x1) H2 wp_code. simpl in wp_code.
destruct x0. destruct x1. destruct x2. simpl in H2.
destruct_opt (V.lvar_assertion_merge class l l0) H3 H2. simpl in H2.
destruct_opt (V.stack_assertion_merge class s s0) H4 H2. simpl in H2.
inversion H2. subst x0 x1. clear H2.
destruct (sem_unpop good_stack wp_code). subst l1. destruct H5. destruct H2. destruct H2. destruct H5.
change V.C.pc_plus_offset with E.C.pc_plus_offset in H.
rewrite H5 in E.
destruct x0; inversion H2; subst o;
[rewrite H in E; normal_continue code_is_safe H1;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p2; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p2; eauto | eauto ]]
|normal_continue code_is_safe H0;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p1; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p1; eauto | eauto ]]].

(* op_ifnull *)
destruct_opt (V.C.pc_plus_offset pc z) H wp_code. 
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H0 wp_code. simpl in wp_code.
destruct_opt (PreV.VA.Cert.lookup cert x) H1 wp_code. simpl in wp_code.
destruct_opt (V.assertion_merge class x0 x1) H2 wp_code. simpl in wp_code.
destruct x0. destruct x1. destruct x2. simpl in H2.
destruct_opt (V.lvar_assertion_merge class l l0) H3 H2. simpl in H2.
destruct_opt (V.stack_assertion_merge class s s0) H4 H2. simpl in H2.
inversion H2. subst x0 x1. clear H2.
destruct (sem_unpop good_stack wp_code). subst l1. destruct H5. destruct H2. destruct H2. destruct H5.
change V.C.pc_plus_offset with E.C.pc_plus_offset in H.
rewrite H5 in E.
destruct x0; inversion H2; subst o;
[normal_continue code_is_safe H0;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p1; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p1; eauto | eauto ]]
|rewrite H in E; normal_continue code_is_safe H1;
 [eapply lvar_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.lvar_assertion_merge_p2; eauto | eauto ]
 |eapply stack_assertion_implication_sound; [ apply subclassing_satisfied | eapply V.stack_assertion_merge_p2; eauto | eauto ]]].

(* op_goto *)
destruct_opt (V.C.pc_plus_offset pc z) H wp_code.
change V.C.pc_plus_offset with E.C.pc_plus_offset in H.
rewrite H in E. normal_continue code_is_safe wp_code.
 
(* op_valreturn *)
destruct current_ty; try discriminate. simpl in wp_code. 
destruct (PreV.VA.value_assertion_eq_dec (V.java_type_to_value_assertion j) (V.stack_type_to_value_assertion s)); try discriminate.
inversion wp_code. subst l2 s2.  
inversion good_stack. subst t a. 

rewrite <- H1 in E. 
destruct fs. inversion frame_stack_is_safe. subst rt final_ty.
right. left. match goal with [H0:E.stop ?st ?v = res |- _ ] => exists st; exists v end.
split. assumption. simpl. rewrite e. assumption.

destruct f. inversion frame_stack_is_safe. normal_continue H11 H12. apply H15; eauto.
 rewrite e. assumption.

(* op_return *)
destruct current_ty; try discriminate. inversion wp_code. subst s2 l2.
destruct fs.
 inversion frame_stack_is_safe. 
 right. left. match goal with [H0:E.stop ?st ?v = res |- _ ] => exists st; exists v end. split; simpl; trivial. 

 destruct f. inversion frame_stack_is_safe. normal_continue H7 H8.

(* op_athrow *)
destruct (option_dec (V.check_exception_handlers code class cert pc (V.C.code_exception_table code))) as [[l exc_check] | exc_check];
  rewrite exc_check in wp_code; [simpl in wp_code|discriminate].
inversion wp_code. subst l2 s2.
inversion good_stack. subst op_stack t a. 
change PreV.VA.va_addr with C.A.va_addr in H2.
inversion H2. 
 (* The exception to be thrown was actually null *)
 subst x v. 
 throw_built_in E E.R.B.java_lang_NullPointerException get_null_pointer_exception preclasses classes heap (preserve_old_classes_id classes) exceptions_exist exc_check subclassing_satisfied code_is_safe.
  apply V.lvar_imp_refl.
 (* There really was an exception to be thrown *)
 subst v nm. rewrite H0 in E. 
 destruct (E.R.Classpool.lookup_informative (E.R.classpool classes) nm') as [[c c_exists] | no_c_exists].
  (* class exists *)
  assert (c_isa_exception:E.R.sub_class classes (E.R.C.class_name c) E.R.B.java_lang_Exception).
   rewrite (E.R.cert_classpool_names_2 c_exists).
   eauto.
  assert (c_isa_throwable:E.R.sub_class classes (E.R.C.class_name c) E.R.B.java_lang_Throwable).
   rewrite (E.R.cert_classpool_names_2 c_exists).
   eapply E.R.sub_class_trans; eauto.
   destruct exceptions_exist as [classes npe cce _ _ _ _ _ _ isa1 isa2 isa].
   assumption.
  rewrite E.R.check_subclass_complete in E; [idtac|assumption].
   destruct (check_exception_handlers_prop _ heap _ _ _ _ _ _ (E.R.cert_classpool_names c_exists) _ _ subclassing_satisfied c_isa_exception exc_check (refl_equal _))
         as [[pc' [l' [s' [search_handlers_ok [cert_lookup_ok [lvar_imp stack_will_be_ok]]]]]] | search_handlers_ok];
    change V.C.code_exception_table with E.R.C.code_exception_table in search_handlers_ok.
    (* Exception is handled in this stack frame *)
    rewrite <- search_handlers_ok in E.
    normal_continue code_is_safe cert_lookup_ok.
     eapply lvar_assertion_implication_sound; eauto.
     apply stack_will_be_ok. eapply ty_sat_addr2. apply H0. 
      change C.class_name with R.C.class_name. rewrite (R.cert_classpool_names_2 c_exists). constructor.
    (* Exception passed upwards *)
    rewrite <- search_handlers_ok in E.
    eapply (unwind_stack_ok preclasses classes heap); eauto.
     eapply ty_sat_addr2. apply H0. change C.class_name with R.C.class_name. rewrite (R.cert_classpool_names_2 c_exists). constructor.
  destruct (heap_good _ _ _ H0) as [[c [c_exists _]] _]. 
   change R.Classpool.lookup with E.R.Classpool.lookup in c_exists.
   change R.classpool with E.R.classpool in c_exists.
   rewrite c_exists in no_c_exists. discriminate.

(* op_iconst *)
destruct_opt (PreV.VA.Cert.lookup cert (S pc)) H wp_code. destruct x.
destruct (sem_unpush subclassing_satisfied good_stack wp_code). subst l. pose (H1 (E.rt_int t) (ty_sat_int _ _ t)). 
normal_continue code_is_safe H.
Save.


End MkVerifierSafety.

End PreVerifierSafety.


















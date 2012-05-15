Require Import BasicMachineTypes.
Require Import ClassDatatypesIface.
Require Import List.
Require Import DestructExt.
Require Import OptionMonad.
Require Import ListExt.
Require Import Store.
Require Import Peano_dec.
Require Import Arith.
Require Import OptionExt.
Require Import Bool.
Require Import FinitePoset.

Module Type VERIFIER.

Declare Module B : BASICS.
Declare Module C : CLASSDATATYPES.

End VERIFIER.

Module MkPreVerifier (B0 : BASICS).

Module B := B0.

Module VA.

Inductive value_assertion : Set :=
  | va_int | va_float | va_null | va_ref | va_double | va_long | va_cat1 | va_cat2 | va_top : value_assertion
  | va_addr : B.Classname.t -> value_assertion.
Definition value_assertion_eq_dec : forall (t1 t2:value_assertion), {t1=t2}+{t1<>t2}.
decide equality. apply B.Classname.eq_dec.
Defined.

Definition stack_assertion := list value_assertion.
Definition lvar_assertion := list value_assertion.
Definition assertion := (lvar_assertion * stack_assertion)%type.

Module NatKey.
Definition t := nat.
Definition eq_dec := eq_nat_dec.
End NatKey.
Module Assertion.
Definition t := assertion.
End Assertion.
Module Cert := Store.MkStore NatKey Assertion.

Inductive constantpool_additional : Set :=
| cpae_static_method | cpae_static_field | cpae_instantiable_class
| cpae_instance_field | cpae_instance_method | cpae_instance_special_method.

Module ConstantPoolAdditionalEntry.
Definition t:= constantpool_additional.
End ConstantPoolAdditionalEntry.
Module ConstantPoolAdditional := Store.MkStore B.ConstantPoolRef ConstantPoolAdditionalEntry.

Module CP := FinitePoset.FinitePoset B.Classname.

Definition code_annotation := unit. (* will be cert *)

Definition method_annotation := unit.

Record class_annotation_aux : Set := mk_class_annotation
  { class_annot_expected_subtypes : CP.t
  ; class_annot_constantpool      : ConstantPoolAdditional.t
  }.

Definition class_annotation := class_annotation_aux.

End VA.

Module MkVerifier (C0 : CLASSDATATYPES with Module B := B with Module A := VA)
                <: VERIFIER with Module B := B with Module C := C0.

Module B := B.
Module C := C0.

Definition java_type_to_value_assertion : C.java_type -> VA.value_assertion :=
  fun ty => match ty with
  | C.ty_byte    => VA.va_int
  | C.ty_char    => VA.va_int
  | C.ty_int     => VA.va_int
  | C.ty_short   => VA.va_int
  | C.ty_boolean => VA.va_int
  | C.ty_float   => VA.va_float
  | C.ty_double  => VA.va_double
  | C.ty_ref x   => VA.va_addr x
  | C.ty_arr _   => VA.va_ref
  | C.ty_long    => VA.va_long
  end.

Section CodeVerification.

Hypothesis code : C.code.
Hypothesis class : C.class.
Hypothesis return_type : option C.java_type.

Definition name_pair_eq_dec : forall (a b:B.Classname.t * B.Classname.t), {a=b}+{a<>b}.
decide equality; apply B.Classname.eq_dec.
Save.

Inductive value_assertion_implication : VA.value_assertion -> VA.value_assertion -> Prop :=
| va_imp_int    : value_assertion_implication VA.va_int VA.va_cat1
| va_imp_null   : value_assertion_implication VA.va_null VA.va_ref
| va_imp_null_2 : forall nm, value_assertion_implication VA.va_null (VA.va_addr nm)
| va_imp_subclass: forall a b,
   VA.CP.leq_prop (VA.class_annot_expected_subtypes (C.class_annotation class)) a b ->
   value_assertion_implication (VA.va_addr a) (VA.va_addr b)
| va_imp_addr   : forall nm, value_assertion_implication (VA.va_addr nm) VA.va_ref
| va_imp_ref    : value_assertion_implication VA.va_ref VA.va_cat1
| va_imp_float  : value_assertion_implication VA.va_float VA.va_cat1
| va_imp_double : value_assertion_implication VA.va_double VA.va_cat2
| va_imp_long   : value_assertion_implication VA.va_long VA.va_cat2
| va_imp_cat1   : value_assertion_implication VA.va_cat1 VA.va_top
| va_imp_cat2   : value_assertion_implication VA.va_cat2 VA.va_top
| va_imp_refl   : forall t, value_assertion_implication t t
| va_imp_trans  : forall t1 t2 t3,
   value_assertion_implication t1 t2 ->
   value_assertion_implication t2 t3 ->
   value_assertion_implication t1 t3.

Hint Resolve va_imp_int va_imp_null va_imp_null_2 va_imp_addr va_imp_ref va_imp_float va_imp_double
             va_imp_long va_imp_cat1 va_imp_cat2 va_imp_refl va_imp_trans.

Inductive stack_assertion_implication : VA.stack_assertion -> VA.stack_assertion -> Prop :=
| stk_imp_nil  : forall s, stack_assertion_implication s nil
| stk_imp_cons : forall t1 t2 s1 s2, value_assertion_implication t1 t2 -> stack_assertion_implication s1 s2 -> stack_assertion_implication (t1::s1) (t2::s2).

Inductive lvar_assertion_implication : VA.lvar_assertion -> VA.lvar_assertion -> Prop :=
| lvar_imp_nil  : lvar_assertion_implication nil nil
| lvar_imp_cons : forall t1 t2 l1 l2, value_assertion_implication t1 t2 -> lvar_assertion_implication l1 l2 -> lvar_assertion_implication (t1::l1) (t2::l2).

Inductive assertion_implication : VA.assertion -> VA.assertion -> Prop :=
| assert_imp : forall l1 l2 s1 s2,
   lvar_assertion_implication l1 l2 ->
   stack_assertion_implication s1 s2 ->
   assertion_implication (l1,s1) (l2,s2).

Lemma value_assertion_implication_top : forall t, value_assertion_implication VA.va_top t -> t = VA.va_top.
intros. set (t':=VA.va_top) in *. set (e:=refl_equal t' : t' = VA.va_top).
generalize t' H e. clear t' H e. intros t' H. induction H; intros; try discriminate.
 reflexivity.
 rewrite (IHvalue_assertion_implication1 e) in IHvalue_assertion_implication2.
 auto.
Save.

Lemma stk_imp_refl : forall s, stack_assertion_implication s s.
intros. induction s. apply stk_imp_nil. apply stk_imp_cons. apply va_imp_refl. apply IHs.
Save.

Lemma lvar_imp_refl : forall l, lvar_assertion_implication l l.
intros. induction l. apply lvar_imp_nil. apply lvar_imp_cons. apply va_imp_refl. apply IHl.
Save.

Lemma lvar_assertion_implication_trans : forall l1 l2 l3,
  lvar_assertion_implication l1 l2 ->
  lvar_assertion_implication l2 l3 ->
  lvar_assertion_implication l1 l3.
intros l1 l2 l3 A. generalize l3. clear l3.
induction A; intros l3 B; inversion B.
 apply lvar_imp_nil. 
 subst. apply lvar_imp_cons. 
  eapply va_imp_trans. apply H. apply H2.
  apply IHA. apply H4.
Save. 

Lemma assert_impl_refl : forall a, assertion_implication a a.
intros. destruct a. apply assert_imp. apply lvar_imp_refl. apply stk_imp_refl. 
Save.

Definition value_assertion_implication_dec : VA.value_assertion -> VA.value_assertion -> bool :=
  fun t1 t2 => match t1, t2 with
  | t, VA.va_top => true
  | t, VA.va_cat1 =>
     match t with
     | VA.va_int => true
     | VA.va_float => true
     | VA.va_null => true
     | VA.va_ref => true
     | VA.va_addr x => true
     | VA.va_cat1 => true
     | _ => false
     end
  | t, VA.va_cat2 =>
     match t with
     | VA.va_long => true
     | VA.va_double => true
     | VA.va_cat2 => true
     | _ => false
     end
  | t, VA.va_ref =>
     match t with
     | VA.va_ref => true
     | VA.va_addr x => true
     | VA.va_null => true
     | _ => false
     end
  | t, VA.va_addr b =>
     match t with
     | VA.va_null => true
     | VA.va_addr a => VA.CP.leq (VA.class_annot_expected_subtypes (C.class_annotation class)) a b
     | _ => false
     end
  | t1, t2 => if VA.value_assertion_eq_dec t1 t2 then true else false
  end.

Lemma value_assertion_implication_dec_sound : forall t1 t2,
  value_assertion_implication_dec t1 t2 = true -> value_assertion_implication t1 t2.
intros; destruct t1; destruct t2; try discriminate; eauto. 
 unfold value_assertion_implication_dec in H. 
 apply va_imp_subclass. apply VA.CP.leq_sound. assumption.
Save.

Lemma value_assertion_implication_dec_refl : forall t, value_assertion_implication_dec t t = true.
destruct t; try reflexivity.
simpl. apply VA.CP.leq_refl. 
Save.

Lemma value_assertion_implication_dec_trans : forall t1 t2 t3,
  value_assertion_implication_dec t1 t2 = true ->
  value_assertion_implication_dec t2 t3 = true ->
  value_assertion_implication_dec t1 t3 = true.
intros. 
destruct t1; destruct t2; try assumption; try discriminate; destruct t3; try discriminate; try reflexivity.
 simpl in *. apply VA.CP.leq_complete. eapply VA.CP.leq_prop_trans. 
  apply VA.CP.leq_sound. apply H.
  apply VA.CP.leq_sound. apply H0.
Save.

Lemma value_assertion_implication_dec_complete : forall t1 t2,
  value_assertion_implication t1 t2 -> value_assertion_implication_dec t1 t2 = true.
intros. induction H; try reflexivity.
 simpl. apply VA.CP.leq_complete. assumption.
 apply value_assertion_implication_dec_refl.
 eapply value_assertion_implication_dec_trans; eauto.
Save.

Fixpoint stack_assertion_implication_dec (s1:VA.stack_assertion) (s2:VA.stack_assertion) {struct s1} : bool :=
  match s1, s2 with
  | s1, nil => true
  | nil, _  => false
  | t1::s1, t2::s2 => if value_assertion_implication_dec t1 t2 then stack_assertion_implication_dec s1 s2 else false
  end.

Lemma stack_assertion_implication_dec_sound : forall s1 s2,
  stack_assertion_implication_dec s1 s2 = true -> stack_assertion_implication s1 s2.
intro; induction s1; intro s2; destruct s2; intro; try discriminate; try constructor;
simpl in H; destruct_bool (value_assertion_implication_dec a v) H0 H.
apply value_assertion_implication_dec_sound. assumption. apply IHs1. assumption.
Save.

Lemma stack_assertion_implication_dec_complete : forall s1 s2,
  stack_assertion_implication s1 s2 -> stack_assertion_implication_dec s1 s2 = true.
intro s1. induction s1; intros; destruct s2; inversion H; trivial.
simpl. rewrite (value_assertion_implication_dec_complete _ _ H3). apply IHs1. apply H5.
Save.

Fixpoint lvar_assertion_implication_dec (l1:VA.lvar_assertion) (l2:VA.lvar_assertion) {struct l1} : bool :=
  match l1, l2 with
  | nil,    nil    => true
  | t1::l1, t2::l2 => if value_assertion_implication_dec t1 t2 then lvar_assertion_implication_dec l1 l2 else false
  | _ ,_           => false
  end.

Lemma lvar_assertion_implication_dec_sound : forall l1 l2,
  lvar_assertion_implication_dec l1 l2 = true -> lvar_assertion_implication l1 l2.
intro; induction l1; intro l2; destruct l2; intro; try discriminate.
apply lvar_imp_nil.
simpl in H. destruct_bool (value_assertion_implication_dec a v) H0 H.
apply lvar_imp_cons. apply value_assertion_implication_dec_sound. apply H0. apply IHl1. apply H.
Save.

Lemma lvar_assertion_implication_dec_complete : forall l1 l2,
  lvar_assertion_implication l1 l2 -> lvar_assertion_implication_dec l1 l2 = true.
intro l1. induction l1; intros; destruct l2; inversion H; trivial.
simpl. rewrite (value_assertion_implication_dec_complete _ _ H3). apply IHl1. apply H5.
Save.

Definition value_assertion_merge : VA.value_assertion -> VA.value_assertion -> option VA.value_assertion :=
  fun t1 t2 =>
  if value_assertion_implication_dec t1 t2 then Some t1
  else if value_assertion_implication_dec t2 t1 then Some t2
  else match t1, t2 with
       | VA.va_addr x, VA.va_addr y => Some VA.va_null
       | _, _ => None
       end.

Lemma value_assertion_merge_p1 : forall t1 t2 t3, value_assertion_merge t1 t2 = Some t3 -> value_assertion_implication t3 t1.
intros. destruct t1; destruct t2; inversion H; eauto.
 unfold value_assertion_merge in H. destruct_bool (value_assertion_implication_dec (VA.va_addr t) (VA.va_addr t0)) H0 H.
  inversion H. auto. 
  destruct_bool (value_assertion_implication_dec (VA.va_addr t0) (VA.va_addr t)) H2 H.
   inversion H. apply value_assertion_implication_dec_sound. assumption. 
   inversion H. auto.
Save.

Lemma value_assertion_merge_p2 : forall t1 t2 t3, value_assertion_merge t1 t2 = Some t3 -> value_assertion_implication t3 t2.
intros. destruct t1; destruct t2; inversion H; eauto. 
 unfold value_assertion_merge in H. destruct_bool (value_assertion_implication_dec (VA.va_addr t) (VA.va_addr t0)) H0 H.
  inversion H. apply value_assertion_implication_dec_sound. assumption. 
  destruct_bool (value_assertion_implication_dec (VA.va_addr t0) (VA.va_addr t)) H2 H.
   inversion H. auto.
   inversion H. auto.
Save.

(*
Lemma value_assertion_and_pair : forall t1 t2 t3 t4,
  value_assertion_implication t4 t1 -> value_assertion_implication t4 t2 ->
  value_assertion_and t1 t2 = Some t3 -> value_assertion_implication t4 t3.
intros. destruct t1; destruct t2; inversion H1; try assumption.
Save.
*)

Fixpoint stack_assertion_merge (s1 s2:VA.stack_assertion) {struct s1} : option VA.stack_assertion :=
  match s1,s2 with
  | nil,   s2     => ret s2
  | s1,    nil    => ret s1
  | t1::s1,t2::s2 =>
     t3 <- value_assertion_merge t1 t2;:
     s <- stack_assertion_merge s1 s2;:
     ret (t3::s)
  end.

Lemma stack_assertion_merge_p1 : forall s1 s2 s3,
  stack_assertion_merge s1 s2 = Some s3 -> stack_assertion_implication s3 s1. 
intros s1. induction s1; intros.
apply stk_imp_nil.
destruct s2; inversion H. apply stk_imp_refl. 
destruct_opt (value_assertion_merge a v) H0 H1. destruct_opt (stack_assertion_merge s1 s2) H2 H1. 
inversion H1. subst s3. apply stk_imp_cons. eapply value_assertion_merge_p1. apply H0.
eapply IHs1. apply H2.
Save.

Lemma stack_assertion_merge_p2 : forall s1 s2 s3,
  stack_assertion_merge s1 s2 = Some s3 -> stack_assertion_implication s3 s2. 
intros s1. induction s1; intros.
destruct s2. apply stk_imp_nil. inversion H. apply stk_imp_refl.
destruct s2; inversion H. 
apply stk_imp_nil.
destruct_opt (value_assertion_merge a v) H0 H1. destruct_opt (stack_assertion_merge s1 s2) H2 H1. 
inversion H1. subst s3. apply stk_imp_cons. eapply value_assertion_merge_p2. apply H0.
eapply IHs1. apply H2.
Save.

Fixpoint lvar_assertion_merge (l1 l2:VA.lvar_assertion) {struct l1} : option VA.lvar_assertion :=
  match l1,l2 with
  | nil,    nil    => ret nil
  | t1::l1, t2::l2 =>
     t3 <- value_assertion_merge t1 t2;:
     l <- lvar_assertion_merge l1 l2;:
     ret (t3::l)
  | _,      _      => fail
  end.

Lemma lvar_assertion_merge_p1 : forall l1 l2 l3,
  lvar_assertion_merge l1 l2 = Some l3 -> lvar_assertion_implication l3 l1.
intros l1. induction l1; intros; destruct l2; try discriminate.
inversion H. apply lvar_imp_nil.
simpl in H. 
destruct_opt (value_assertion_merge a v) H0 H. destruct_opt (lvar_assertion_merge l1 l2) H1 H. inversion H.
subst l3. apply lvar_imp_cons. eapply value_assertion_merge_p1. apply H0. eapply IHl1. apply H1.
Save.

Lemma lvar_assertion_merge_p2 : forall l1 l2 l3,
  lvar_assertion_merge l1 l2 = Some l3 -> lvar_assertion_implication l3 l2.
intros l1. induction l1; intros; destruct l2; try discriminate.
inversion H. apply lvar_imp_nil.
simpl in H. 
destruct_opt (value_assertion_merge a v) H0 H. destruct_opt (lvar_assertion_merge l1 l2) H1 H. inversion H.
subst l3. apply lvar_imp_cons. eapply value_assertion_merge_p2. apply H0. eapply IHl1. apply H1.
Save.

Definition assertion_merge : VA.assertion -> VA.assertion -> option VA.assertion :=
  fun a1 a2 => match a1,a2 with
  | (l1,s1), (l2,s2) =>
     l <- lvar_assertion_merge l1 l2;:
     s <- stack_assertion_merge s1 s2;:
     ret (l,s)
  end.


Lemma java_type_category_correct1 : forall ty, C.java_type_category ty = C.category1 -> value_assertion_implication (java_type_to_value_assertion ty) VA.va_cat1.
intros. destruct ty; try discriminate; simpl; eauto.
Save.

Lemma java_type_category_correct2 : forall ty, C.java_type_category ty = C.category2 -> value_assertion_implication (java_type_to_value_assertion ty) VA.va_cat2.
intros. destruct ty; try discriminate; constructor.
Save.


Definition cert_incl := fun c1 c2 => forall n, option_incl (VA.Cert.lookup c1 n) (VA.Cert.lookup c2 n).

Lemma cert_incl_refl : forall c, cert_incl c c.
unfold cert_incl. intros. apply option_incl_refl.
Save.

Lemma cert_incl_trans : forall c1 c2 c3, cert_incl c1 c2 -> cert_incl c2 c3 -> cert_incl c1 c3.
unfold cert_incl. intros. 
eapply option_incl_trans. apply H. apply H0.
Save.

Lemma cert_incl_update : forall c n a, VA.Cert.lookup c n = None -> cert_incl c (VA.Cert.update c n a).
unfold cert_incl. intros.
destruct (eq_nat_dec n n0). 
subst n. rewrite H. rewrite VA.Cert.lookup_update. apply o_inc_2.
rewrite VA.Cert.indep_lookup. apply option_incl_refl. assumption.
Save.

Lemma cert_incl_lookup : forall c1 c2 n a, VA.Cert.lookup c1 n = Some a -> cert_incl c1 c2 -> VA.Cert.lookup c2 n = Some a.
intros. unfold cert_incl in H0. 
set (H1:=H0 n). rewrite H in H1. inversion H1. trivial.
Save.

Definition stack_type_to_value_assertion : C.stack_type -> VA.value_assertion :=
  fun sty => match sty with
  | C.sty_int => VA.va_int
  | C.sty_long => VA.va_long
  | C.sty_double => VA.va_double
  | C.sty_float => VA.va_float
  | C.sty_addr => VA.va_ref
  end.

Definition unpush : VA.value_assertion -> VA.assertion -> option VA.assertion :=
  fun t a =>
  match a with
  | (l, nil) => None
  | (l, t'::s') => if value_assertion_implication_dec t t' then Some (l, s') else None
  end.

Definition unpush_2 : VA.assertion -> option (VA.value_assertion * VA.assertion) :=
  fun a =>
  match a with
  | (l, nil) => None
  | (l, t::s) => Some (t, (l,s))
  end.

Definition unpop : VA.value_assertion -> VA.assertion -> option VA.assertion :=
  fun t a => let (l, s) := a in Some (l, t::s).

Definition unstore : nat -> VA.assertion -> bool -> option (VA.value_assertion * VA.assertion) :=
  fun n a is_cat2 =>
  let (l, s) := a in
  match n with
  | 0 => ret tt
  | S nm1 =>
     tnm1 <- nth_error l nm1;:
     if value_assertion_implication_dec tnm1 VA.va_cat2 then fail else ret tt
  end;;
  t <- nth_error l n;:
  (if (*value_assertion_implication_dec t va_cat2*) is_cat2 then
     tnp1 <- nth_error l (S n);:
     if VA.value_assertion_eq_dec tnp1 VA.va_top then ret tt else fail
  else
     ret tt);;
  l' <- list_update l n VA.va_top;:
  ret (t, (l', s)).

(*
Definition unstore : nat -> value_assertion -> assertion -> option assertion :=
  fun n t a =>
  if value_assertion_eq_dec t va_top then fail else
  let (l,s) := a in
  match n with
  | 0 => ret tt
  | S nm1 =>
     tnm1 <- nth_error l nm1;:
     if value_assertion_implication_dec tnm1 va_cat2 then fail else ret tt
  end;;
  t' <- nth_error l n;:
  if value_assertion_implication_dec t t' then
     (if value_assertion_implication_dec t va_cat2 then
         tnp1 <- nth_error l (S n);:
         if value_assertion_eq_dec tnp1 va_top then ret tt else fail
      else
         ret tt);;
     l' <- list_update l n va_top;:
     ret (l', s)
  else
     fail.
*)
Definition unretrieve : VA.value_assertion -> nat -> VA.assertion -> option VA.assertion :=
  fun t n a =>
  let (l, s) := a in
  t' <- nth_error l n;:
  t'' <- value_assertion_merge t t';:
  l <- list_update l n t'';:
  ret (l,s).

Fixpoint general_lvar_assertion (size:nat) : VA.lvar_assertion :=
 match size with
 | 0   => nil
 | S n => VA.va_top::general_lvar_assertion n
 end.

Definition stack_type_is_cat2 : C.stack_type -> bool :=
  fun ty => match C.stack_type_category ty with
  | C.category1 => false
  | C.category2 => true
  end.

Fixpoint check_exception_handlers (cert:VA.Cert.t) (pc:nat) (handlers:list C.exception_handler) {struct handlers} : option VA.lvar_assertion :=
  match handlers with
  | nil => Some (general_lvar_assertion (C.code_max_lvars code))
  | C.mkExcHandler start_pc end_pc handler_pc opt_type_idx::handlers =>
     l' <- check_exception_handlers cert pc handlers;:
     (if C.is_within start_pc end_pc pc then
        a <- VA.Cert.lookup cert handler_pc;:
        let (l,s) := a in
        s' <- (match opt_type_idx with
               | None     => ret (VA.va_addr B.java_lang_Exception::nil)     (* FIXME: this is a temporary fix (should be j.l.Throwable) to compensate for our over-eager constraints on athrow *)
               | Some idx =>
                  ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
                  match ref with
                  | C.cpe_classref clsname => ret (VA.va_addr clsname::nil)
                  | _ => fail
                  end
               end);:
        lift_bool (stack_assertion_implication_dec s' s);;
        lvar_assertion_merge l' l
      else
        ret l')
  end.

Definition wp : VA.Cert.t -> nat -> C.opcode -> option VA.assertion :=
  fun cert pc op =>
  match op with
  (* Constants *)
  | C.op_iconst i =>
     a <- VA.Cert.lookup cert (S pc);:
     unpush VA.va_int a
  | C.op_load ty n =>
     a <- VA.Cert.lookup cert (S pc);:
     x <- unpush_2 a;:
     let (ty', a) := x in
     lift_bool (value_assertion_implication_dec ty' (stack_type_to_value_assertion ty));;     
     unretrieve ty' n a
  | C.op_store ty n =>
     a <- VA.Cert.lookup cert (S pc);:
     x <- unstore n a (stack_type_is_cat2 ty);:
     let (ty', a) := x in
     ty'' <- value_assertion_merge (stack_type_to_value_assertion ty) ty';:
     unpop ty'' a
  | C.op_iarithb op =>
     match op with
     | C.iadd => Some tt | C.imul => Some tt
     | C.isub => Some tt | C.iand => Some tt
     | C.ior  => Some tt | C.ixor => Some tt
     | _ => None end;;
     a <- VA.Cert.lookup cert (S pc);:
     a <- unpush VA.va_int a;:
     a <- unpop VA.va_int a;:
     unpop VA.va_int a
  | C.op_iarithu op =>
     a <- VA.Cert.lookup cert (S pc);:
     a <- unpush VA.va_int a;:
     unpop VA.va_int a
  | C.op_goto offset =>
     new_pc <- C.pc_plus_offset pc offset;:
     VA.Cert.lookup cert new_pc
  | C.op_valreturn ty =>
     rt <- return_type;:
     let lty := stack_type_to_value_assertion ty in
     if VA.value_assertion_eq_dec (java_type_to_value_assertion rt) lty then
        ret (general_lvar_assertion (C.code_max_lvars code), lty::nil)
     else
        fail
  | C.op_return =>
     match return_type with None => ret tt | Some _ => fail end;;
     ret (general_lvar_assertion (C.code_max_lvars code), nil)
  | C.op_if _ offset =>
     target <- C.pc_plus_offset pc offset;:
     a1 <- VA.Cert.lookup cert (S pc);:
     a2 <- VA.Cert.lookup cert target;:
     a <- assertion_merge a1 a2;:
     unpop VA.va_int a
  | C.op_ifnonnull offset =>
     target <- C.pc_plus_offset pc offset;:
     a1 <- VA.Cert.lookup cert (S pc);:
     a2 <- VA.Cert.lookup cert target;:
     a <- assertion_merge a1 a2;:
     unpop VA.va_ref a
  | C.op_ifnull offset =>
     target <- C.pc_plus_offset pc offset;:
     a1 <- VA.Cert.lookup cert (S pc);:
     a2 <- VA.Cert.lookup cert target;:
     a <- assertion_merge a1 a2;:
     unpop VA.va_ref a
  | C.op_if_icmp _ offset =>
     target <- C.pc_plus_offset pc offset;:
     a1 <- VA.Cert.lookup cert (S pc);:
     a2 <- VA.Cert.lookup cert target;:
     a <- assertion_merge a1 a2;:
     a <- unpop VA.va_int a;:
     unpop VA.va_int a
  | C.op_if_acmp _ offset =>
     target <- C.pc_plus_offset pc offset;:
     a1 <- VA.Cert.lookup cert (S pc);:
     a2 <- VA.Cert.lookup cert target;:
     a <- assertion_merge a1 a2;:
     a <- unpop VA.va_ref a;:
     unpop VA.va_ref a
  | C.op_nop =>
     VA.Cert.lookup cert (S pc)
  | C.op_pop =>
     a <- VA.Cert.lookup cert (S pc);:
     unpop VA.va_cat1 a
  | C.op_dup =>
     a <- VA.Cert.lookup cert (S pc);:
     x1 <- unpush_2 a;:
     let (v1,a) := x1 in
     x2 <- unpush_2 a;:
     let (v2,a) := x2 in
     v <- value_assertion_merge v1 v2;:
     if value_assertion_implication_dec v VA.va_cat1 then
        unpop v a
     else
        fail
  | C.op_iinc n _ =>
     a <- VA.Cert.lookup cert (S pc);:
     x <- unstore n a false;:
     let (ty, a) := x in
     (if VA.value_assertion_eq_dec ty VA.va_int then ret tt else fail);; (* FIXME: too strong? *)
     unretrieve VA.va_int n a
  | C.op_aconst_null =>
     a <- VA.Cert.lookup cert (S pc);:
     unpush VA.va_null a
  | C.op_invokestatic idx =>
     a <- VA.Cert.lookup cert (S pc);:
     exc_l <- check_exception_handlers cert pc (C.code_exception_table code);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     type <- VA.ConstantPoolAdditional.lookup (VA.class_annot_constantpool (C.class_annotation class)) idx;:
     match ref, type with
     | C.cpe_methodref clsname methname methdescrip, VA.cpae_static_method =>
        req_stack <- ret (rev (map java_type_to_value_assertion (C.descriptor_arg_types methdescrip)));:
        a <- match C.descriptor_ret_type methdescrip with
             | None => ret a
             | Some ty => unpush (java_type_to_value_assertion ty) a
             end;:
        let (l, s) := a in
        l' <- lvar_assertion_merge l exc_l;:
        ret (l', req_stack ++ s)
     | _,_ => fail
     end
  | C.op_invokespecial idx =>
     a <- VA.Cert.lookup cert (S pc);:
     exc_l <- check_exception_handlers cert pc (C.code_exception_table code);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     type <- VA.ConstantPoolAdditional.lookup (VA.class_annot_constantpool (C.class_annotation class)) idx;:
     match ref, type with
     | C.cpe_methodref clsname methname methdescrip, VA.cpae_instance_special_method =>
        req_stack <- ret (rev (map java_type_to_value_assertion (C.descriptor_arg_types methdescrip)));:
        a <- match C.descriptor_ret_type methdescrip with
             | None => ret a
             | Some ty => unpush (java_type_to_value_assertion ty) a
             end;:
        let (l,s) := a in
        l' <- lvar_assertion_merge l exc_l;:
        ret (l', req_stack ++ VA.va_addr clsname::s)
     | _,_ => fail
     end
(*  | C.op_invokevirtual idx =>
     a <- VA.Cert.lookup cert (S pc);:
     exc_l <- check_exception_handlers cert pc (C.code_exception_table code);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     type <- VA.ConstantPoolAdditional.lookup (VA.class_annot_constantpool (C.class_annotation class)) idx;:
     match ref, type with
     | C.cpe_methodref clsname methname methdescrip, VA.cpae_instance_method =>
        req_stack <- ret (rev (map java_type_to_value_assertion (C.descriptor_arg_types methdescrip)));:
        a <- match C.descriptor_ret_type methdescrip with
             | None => ret a
             | Some ty => unpush (java_type_to_value_assertion ty) a
             end;:
        let (l,s) := a in
        l' <- lvar_assertion_merge l exc_l;:
        ret (l', req_stack ++ VA.va_addr clsname::s)
     | _,_ => fail
     end *)
  | C.op_getstatic idx =>
     a <- VA.Cert.lookup cert (S pc);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     type <- VA.ConstantPoolAdditional.lookup (VA.class_annot_constantpool (C.class_annotation class)) idx;:
     match ref, type with
     | C.cpe_fieldref clsname fieldname fieldty, VA.cpae_static_field =>
        unpush (java_type_to_value_assertion fieldty) a
     | _,_ => fail
     end
  | C.op_putstatic idx =>
     a <- VA.Cert.lookup cert (S pc);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     type <- VA.ConstantPoolAdditional.lookup (VA.class_annot_constantpool (C.class_annotation class)) idx;:
     match ref, type with
     | C.cpe_fieldref clsname fieldname fieldty, VA.cpae_static_field =>
        unpop (java_type_to_value_assertion fieldty) a
     | _,_ => fail
     end
  | C.op_new idx =>
     a <- VA.Cert.lookup cert (S pc);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     type <- VA.ConstantPoolAdditional.lookup (VA.class_annot_constantpool (C.class_annotation class)) idx;:
     match ref, type with
     | C.cpe_classref clsname, VA.cpae_instantiable_class =>
        unpush (VA.va_addr clsname) a
     | _,_ => fail
     end
  | C.op_putfield idx =>
     a <- VA.Cert.lookup cert (S pc);:
     exc_l <- check_exception_handlers cert pc (C.code_exception_table code);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     type <- VA.ConstantPoolAdditional.lookup (VA.class_annot_constantpool (C.class_annotation class)) idx;:
     match ref, type with
     | C.cpe_fieldref clsname fieldname fieldty, VA.cpae_instance_field =>
        a <- unpop (VA.va_addr clsname) a;:
        a <- unpop (java_type_to_value_assertion fieldty) a;:
        let (l,s) := a in
        l' <- lvar_assertion_merge l exc_l;:
        ret (l', s)
     | _,_ => fail
     end
  | C.op_getfield idx =>
     a <- VA.Cert.lookup cert (S pc);:
     exc_l <- check_exception_handlers cert pc (C.code_exception_table code);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     type <- VA.ConstantPoolAdditional.lookup (VA.class_annot_constantpool (C.class_annotation class)) idx;:
     match ref, type with
     | C.cpe_fieldref clsname fieldname fieldty, VA.cpae_instance_field =>
        a <- unpush (java_type_to_value_assertion fieldty) a;:
        a <- unpop (VA.va_addr clsname) a;:
        let (l,s) := a in
        l' <- lvar_assertion_merge l exc_l;:
        ret (l', s)
     | _,_ => fail
     end
  | C.op_athrow =>
     l <- check_exception_handlers cert pc (C.code_exception_table code);:
     ret (l, VA.va_addr B.java_lang_Exception::nil)
  | C.op_instanceof idx =>
     a <- VA.Cert.lookup cert (S pc);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     match ref with
     | C.cpe_classref clsname =>
        a <- unpush VA.va_int a;:
        unpop VA.va_ref a
     | _ => fail
     end
  | C.op_checkcast idx =>
     a <- VA.Cert.lookup cert (S pc);:
     exc_l <- check_exception_handlers cert pc (C.code_exception_table code);:
     ref <- C.ConstantPool.lookup (C.class_constantpool class) idx;:
     match ref with
     | C.cpe_classref clsname =>
        a <- unpush (VA.va_addr clsname) a;:
        a <- unpop VA.va_ref a;:
        let (l,s) := a in
        l' <- lvar_assertion_merge l exc_l;:
        ret (l', s)
     | _ => fail
     end
  | _ => None
  end.

Inductive safe_instruction : VA.Cert.t -> nat -> C.opcode -> Prop :=
  mk_safe_instruction : forall cert pc op s1 s2 l1 l2,
    VA.Cert.lookup cert pc = Some (l1, s1) ->
    wp cert pc op = Some (l2, s2) ->
    lvar_assertion_implication l1 l2 ->
    stack_assertion_implication s1 s2 ->
    safe_instruction cert pc op.

Inductive safe_code : VA.Cert.t -> Prop :=
  mk_safe_code : forall cert,
    (forall n a, VA.Cert.lookup cert n = Some a -> n < length (C.code_code code)) ->
    (forall n op, nth_error (C.code_code code) n = Some op -> safe_instruction cert n op) ->
    safe_code cert.

Definition completion_step : VA.Cert.t -> nat -> C.opcode -> option VA.Cert.t :=
  fun cert pc op =>
  a <- wp cert pc op;:
  match VA.Cert.lookup cert pc with
  | None => ret (VA.Cert.update cert pc a)
  | Some a' =>
     match a', a with
     | (l',s'), (l,s) => if lvar_assertion_implication_dec l' l then if stack_assertion_implication_dec s' s then ret cert else fail else fail
     end
  end.

Fixpoint complete_cert_aux (ops:list C.opcode) (cert:VA.Cert.t) (pc:nat) {struct ops} : option VA.Cert.t :=
  match ops with
  | nil     => None
  | op::nil => completion_step cert pc op 
  | op::ops => cert' <- complete_cert_aux ops cert (S pc);: completion_step cert' pc op
  end.

Definition clean_cert : VA.Cert.t -> nat -> VA.Cert.t :=
  fun cert limit =>
    VA.Cert.remove_by (fun n => if le_lt_dec limit n then true else false) cert.

Definition complete_cert : VA.Cert.t -> option VA.Cert.t :=
  fun cert =>
    complete_cert_aux (C.code_code code) (clean_cert cert (length (C.code_code code))) 0.

Lemma clean_ok : forall cert limit n, n >= limit -> VA.Cert.lookup (clean_cert cert limit) n = None.
intros. unfold clean_cert. apply VA.Cert.remove_by_lookup.
destruct (le_lt_dec limit n) as [limit_le_n | n_lt_limit].
 reflexivity.
 elimtype False. omega.
Save.

Lemma clean_contra : forall c limit, (forall n, n >= limit -> VA.Cert.lookup c n = None) ->
  (forall n x, VA.Cert.lookup c n = Some x -> n < limit).
intros. 
destruct (dec_lt n limit). assumption.
assert (n >= limit). omega. rewrite (H n H2) in H0. discriminate.
Save.

Lemma step_incl : forall c c' n op, completion_step c n op = Some c' -> cert_incl c c'.
intros. unfold completion_step in H.
destruct (wp c n op); try discriminate.
destruct_opt (VA.Cert.lookup c n) H0 H; simpl in H. destruct x. destruct a.
destruct (lvar_assertion_implication_dec l l0); try discriminate.
destruct (stack_assertion_implication_dec s s0); try discriminate.
inversion H. subst c. apply cert_incl_refl.
inversion H. apply cert_incl_update. apply H0.
Save.

Lemma complete_cert_incl : forall c c' n ops, complete_cert_aux ops c n = Some c' -> cert_incl c c'.
intros. generalize n c' H. clear n c' H.
induction ops; intros.
discriminate.
simpl in H.
destruct ops. eapply step_incl. apply H.
destruct_opt (complete_cert_aux (o::ops) c (S n)) H0 H.
simpl in H. eapply cert_incl_trans. eapply IHops. apply H0. eapply step_incl. apply H.
Save.

Lemma complete_cert_aux_prop : forall n ops c c', n < length ops ->
  complete_cert_aux ops c 0 = Some c' ->
  (exists c'', complete_cert_aux (tail n ops) c n = Some c'' /\ cert_incl c c'' /\ cert_incl c'' c').
intros. 
rewrite <- (tail_0 ops) in H0.
pose (n':=n). assert (n'<=n). auto with arith. replace 0 with (n-n') in H0.
pose (c3:=c'). assert (cert_incl c3 c'). apply cert_incl_refl. replace c' with c3 in H0.
generalize c c3 H2 H0 H1. clear c c3 H2 H0 H1. induction n'; intros.
rewrite <- minus_n_O in H0. exists c3. 
split. assumption. split. eapply complete_cert_incl. apply H0. apply H2.
destruct (tail_minus ops n' n). omega. assumption. rewrite H3 in H0. 
simpl in H0. 
destruct (tail_S (n-n') ops). omega.
rewrite H4 in H0. destruct_opt (complete_cert_aux (x0 :: tail (S (n - n')) ops) c (S (n - S n'))) H5 H0.
rewrite <- H4 in H5. replace (S (n - S n')) with (n-n') in H5. 
eapply IHn'. eapply cert_incl_trans. eapply step_incl. simpl in H0. apply H0. apply H2. apply H5.
omega. omega. trivial. replace n with n'. omega. trivial. 
Save.

Lemma completion_step_clean : forall c c' pc op limit,
  pc < limit ->
  completion_step c pc op = Some c' ->
  (forall n, n >= limit -> VA.Cert.lookup c n = None) ->
  (forall n, n >= limit -> VA.Cert.lookup c' n = None).
intros.
unfold completion_step in H0. 
destruct (wp c pc op); try discriminate. 
destruct (VA.Cert.lookup c pc). 
destruct o. simpl in H0. destruct a.
destruct (lvar_assertion_implication_dec l l0); try discriminate.
destruct (stack_assertion_implication_dec s s0); try discriminate. inversion H0. subst c'.
apply H1. apply H2.
inversion H0. assert (pc<>n). omega.
rewrite (VA.Cert.indep_lookup c _ _ a H3).
apply H1. apply H2.
Save.

Lemma complete_cert_aux_clean : forall c c' n ops, 
  (forall m, m >= n+length ops -> VA.Cert.lookup c m = None) ->
  complete_cert_aux ops c n = Some c' -> 
  (forall m, m >= n+length ops -> VA.Cert.lookup c' m = None).
intros. generalize n c' H H0 m H1. clear n c' H H0 m H1.
induction ops; intros.
discriminate.
simpl in H0.
destruct ops. apply (completion_step_clean c c' n a (n+length (a::nil))). simpl. omega. apply H0. apply H. apply H1.
destruct_opt (complete_cert_aux (o::ops) c (S n)) H2 H0.
simpl in H0.  
apply (completion_step_clean x c' n a (n+length (a::o::ops))). simpl. omega. apply H0. 
intros. eapply (IHops (S n)). intros. apply H. simpl. simpl in H4. omega. apply H2. 
simpl in * |- *. omega.
assumption.
Save.

Lemma incl_check_exception_handlers : forall c1 c2 n handlers l,
  cert_incl c1 c2 ->
  check_exception_handlers c1 n handlers = Some l ->
  check_exception_handlers c2 n handlers = Some l.
intros c1 c2 n handlers l c1_incl_c2. generalize l. clear l.
induction handlers; simpl in *; intros l old_check.
 (* Base case *)
 assumption.
 (* Step case *)
 destruct a as [start_pc end_pc handler_pc opt_type_idx].
 destruct (option_dec (check_exception_handlers c1 n handlers)) as [[l' step_check_ok] | step_check_fail].
  (* checking the rest succeeded *)
  rewrite step_check_ok in old_check. rewrite (IHhandlers l' step_check_ok). 
  simpl in *. 
  destruct (C.is_within start_pc end_pc n) as [is_within|is_without].
   (* handler applies *)
   destruct (option_dec (VA.Cert.lookup c1 handler_pc)) as [[a cert_lookup_ok] | cert_lookup_fail].
    (* cert lookup ok *)
    rewrite cert_lookup_ok in old_check. rewrite (cert_incl_lookup _ _ _ _ cert_lookup_ok c1_incl_c2).
    assumption.
    (* cert lookup failed: unpossible *)
    rewrite cert_lookup_fail in old_check. discriminate.
   (* handler does not apply *)
   assumption.
  (* checking the rest failed *)
  rewrite step_check_fail in old_check. discriminate.
Save.

Lemma cert_incl_wp : forall c1 c2 n op a, wp c1 n op = Some a -> cert_incl c1 c2 -> wp c2 n op = Some a.
intros.
destruct op; simpl in * |- *;
 first [ discriminate
       | assumption
       | try (destruct i; try discriminate; simpl);
         destruct_opt (VA.Cert.lookup c1 (S n)) H1 H; rewrite (cert_incl_lookup c1 c2 (S n) x H1 H0); apply H
       | destruct_opt (C.pc_plus_offset n z) H1 H; rewrite H1; 
         destruct_opt (VA.Cert.lookup c1 (S n)) H2 H; rewrite (cert_incl_lookup c1 c2 (S n) x0 H2 H0); simpl in * |- *;
         destruct_opt (VA.Cert.lookup c1 x) H3 H; rewrite (cert_incl_lookup c1 c2 x x1 H3 H0); simpl in * |- *;
         apply H
       | destruct_opt (C.pc_plus_offset n z) H1 H; rewrite H1; simpl in * |- *; eapply cert_incl_lookup; [apply H|apply H0]
       | destruct_opt (VA.Cert.lookup c1 (S n)) H1 H; rewrite (cert_incl_lookup c1 c2 (S n) x H1 H0);
         destruct_opt (check_exception_handlers c1 n (C.code_exception_table code)) H2 H;
         rewrite (incl_check_exception_handlers _ _ _ _ _ H0 H2); assumption
       | destruct_opt (check_exception_handlers c1 n (C.code_exception_table code)) H1 H;
         rewrite (incl_check_exception_handlers _ _ _ _ _ H0 H1); assumption ].
Save.

Lemma cert_update_wp : forall c n op a,
     VA.Cert.lookup c n = None -> wp c n op = Some a -> wp (VA.Cert.update c n a) n op = Some a.
intros. eapply cert_incl_wp. apply H0. apply cert_incl_update. apply H.
Save.

Lemma step_ok : forall c c' op pc, completion_step c pc op = Some c' -> safe_instruction c' pc op.
intros. unfold completion_step in H.
destruct_opt (wp c pc op) H0 H. destruct x.
destruct_opt (VA.Cert.lookup c pc) H1 H; simpl in H. destruct x.
destruct_bool (lvar_assertion_implication_dec l0 l) H2 H. 
destruct_bool (stack_assertion_implication_dec s0 s) H3 H.
inversion H. subst c.
eapply mk_safe_instruction. 
  apply H1. apply H0. apply lvar_assertion_implication_dec_sound. assumption. apply stack_assertion_implication_dec_sound. assumption.
inversion H. 
eapply mk_safe_instruction. 
apply VA.Cert.lookup_update. apply cert_update_wp. apply H1. apply H0.
apply lvar_imp_refl. apply stk_imp_refl.
Save.

Lemma cert_incl_safe : forall c1 c2 pc op,
   safe_instruction c1 pc op -> cert_incl c1 c2 -> safe_instruction c2 pc op.
intros.
inversion H. 
eapply mk_safe_instruction. 
  eapply cert_incl_lookup. apply H1. apply H0.
  eapply cert_incl_wp. apply H2. apply H0.
  assumption.
  assumption.
Save.

Lemma complete_cert_ok : forall c c', complete_cert c = Some c' -> safe_code c'.
intros. unfold complete_cert in H.
eapply mk_safe_code. 
apply clean_contra. intros. 
apply (complete_cert_aux_clean (clean_cert c (length (C.code_code code))) c' 0 (C.code_code code)). 
intros. apply clean_ok. assumption. apply H. simpl. assumption.
intros. 
destruct (complete_cert_aux_prop n (C.code_code code) _ c' (nth_error_length_2 _ _ _ _ H0) H). destruct H1. destruct H2.
destruct (tail_nth_error n (C.code_code code) op H0).
rewrite H4 in H1. simpl in H1. 
destruct x0. 
eapply cert_incl_safe. eapply step_ok. apply H1. apply H3.
destruct_opt (complete_cert_aux (o::x0) (clean_cert c (length (C.code_code code))) (S n)) H5 H1. 
simpl in H1. eapply cert_incl_safe. eapply step_ok. apply H1. apply H3. 
Save.

End CodeVerification.

Fixpoint arg_tys_to_lvar_assertion (arg_tys:list C.java_type) (required_lvars:nat) {struct arg_tys} : option (list VA.value_assertion) :=
  match arg_tys with
  | nil      => Some (general_lvar_assertion required_lvars)
  | ty::arg_tys =>
     match C.java_type_category ty, required_lvars with
     | C.category1, S n     => 
        match arg_tys_to_lvar_assertion arg_tys n with
        | None => None
        | Some a => Some (java_type_to_value_assertion ty::a)
        end
     | C.category2, S (S n) =>
        match arg_tys_to_lvar_assertion arg_tys n with
        | None => None
        | Some a => Some (java_type_to_value_assertion ty::VA.va_top::a)
        end
     | _, _ => None
     end
  end.

Inductive static_method_verified : C.class -> C.method -> C.descriptor -> Prop :=
  mk_static_method_verified : forall method class md cert l s code l',
    C.method_code method = Some code ->
    safe_code code class (C.descriptor_ret_type md) cert ->
    VA.Cert.lookup cert 0 = Some (l, s) ->
    arg_tys_to_lvar_assertion (C.descriptor_arg_types md) (C.code_max_lvars code) = Some l' ->
    lvar_assertion_implication class l' l ->
    stack_assertion_implication class nil s ->
    static_method_verified class method md.

Inductive instance_method_verified : C.class -> C.method -> C.descriptor -> Prop :=
  mk_instance_method_verified : forall method class md cert l s code l',
    C.method_abstract method = false ->
    C.method_code method = Some code ->
    safe_code code class (C.descriptor_ret_type md) cert ->
    VA.Cert.lookup cert 0 = Some (l, s) ->
    arg_tys_to_lvar_assertion (C.ty_ref (C.class_name class)::C.descriptor_arg_types md) (C.code_max_lvars code) = Some l' ->
    lvar_assertion_implication class l' l ->
    stack_assertion_implication class nil s ->
    instance_method_verified class method md.


Inductive class_verified : C.class -> Prop :=
  mk_class_verified : forall class,
    (forall mn md method,
       C.MethodList.lookup (C.class_methods class) (mn,md) = Some method ->
       (C.method_static method = true ->
        static_method_verified class method md)
       /\
       (C.method_static method = false ->
        instance_method_verified class method md)) ->
    class_verified class.

Definition is_nil : forall (A:Set), list A -> bool :=
  fun A l => match l with
  | nil =>true
  | _ => false
  end.
Implicit Arguments is_nil [A].

Definition verify_static_method : C.class -> C.method -> C.descriptor -> bool :=
  fun class method md => match
    code <- C.method_code method;:
    cert <- complete_cert code class (C.descriptor_ret_type md) VA.Cert.empty;:
    a <- VA.Cert.lookup cert 0;:
    let (l,s) := a in
    l' <- arg_tys_to_lvar_assertion (C.descriptor_arg_types md) (C.code_max_lvars code);:
    lift_bool (lvar_assertion_implication_dec class l' l);;
    lift_bool (stack_assertion_implication_dec class nil s) with Some tt => true | None => false end.

Lemma verify_static_method_sound : forall class method md,
  verify_static_method class method md = true -> static_method_verified class method md.
intros. unfold verify_static_method in H.
destruct_opt (C.method_code method) H0 H. simpl in H. 
destruct_opt (complete_cert x class (C.descriptor_ret_type md) VA.Cert.empty) H1 H. simpl in H.
destruct_opt (VA.Cert.lookup x0 0) H2 H. simpl in H.
destruct x1.
destruct_opt (arg_tys_to_lvar_assertion (C.descriptor_arg_types md) (C.code_max_lvars x)) H3 H. simpl in H.
destruct_bool (lvar_assertion_implication_dec class x1 l) H4 H. simpl in H.
change (match s with nil => true | _::_ => false end) with (stack_assertion_implication_dec class nil s) in H.
destruct_bool (stack_assertion_implication_dec class nil s) H5 H.
eapply mk_static_method_verified; eauto.
 eapply complete_cert_ok. apply H1. 
 apply lvar_assertion_implication_dec_sound. apply H4.
 apply stack_assertion_implication_dec_sound. apply H5.
Save.

Definition verify_instance_method : C.class -> C.method -> C.descriptor -> bool :=
  fun class method md => match
    lift_bool (negb (C.method_abstract method));;
    code <- C.method_code method;:
    cert <- complete_cert code class (C.descriptor_ret_type md) VA.Cert.empty;:
    a <- VA.Cert.lookup cert 0;:
    let (l,s) := a in
    l' <- arg_tys_to_lvar_assertion (C.ty_ref (C.class_name class)::C.descriptor_arg_types md) (C.code_max_lvars code);:
    lift_bool (lvar_assertion_implication_dec class l' l);;
    lift_bool (stack_assertion_implication_dec class nil s) with Some tt => true | None => false end.

Lemma verify_instance_method_sound : forall class method md,
  verify_instance_method class method md = true -> instance_method_verified class method md.
intros. unfold verify_instance_method in H.
destruct_bool (C.method_abstract method) H0 H. simpl in H.
destruct_opt (C.method_code method) H1 H. simpl in H. 
destruct_opt (complete_cert x class (C.descriptor_ret_type md) VA.Cert.empty) H2 H. simpl in H.
destruct_opt (VA.Cert.lookup x0 0) H3 H. simpl in H.
destruct x1.
destruct (option_dec (arg_tys_to_lvar_assertion (C.ty_ref (C.class_name class)::C.descriptor_arg_types md) (C.code_max_lvars x))); try (simpl in H4; rewrite H4 in H; discriminate).
 destruct H4. simpl in H4. rewrite H4 in H. simpl in H.
destruct_bool (lvar_assertion_implication_dec class x1 l) H5 H. simpl in H.
change (match s with nil => true | _::_ => false end) with (stack_assertion_implication_dec class nil s) in H.
destruct_bool (stack_assertion_implication_dec class nil s) H6 H.
eapply mk_instance_method_verified; eauto.
 eapply complete_cert_ok. apply H2. 
 apply lvar_assertion_implication_dec_sound. apply H5.
 apply stack_assertion_implication_dec_sound. apply H6.
Save.

Hint Resolve verify_static_method_sound verify_instance_method_sound.

Definition verify_class : C.class -> bool :=
  fun class =>
    C.MethodList.check_all (C.class_methods class)
                           (fun d method => if C.method_static method then
                                               verify_static_method class method (snd d)
                                            else
                                               verify_instance_method class method (snd d)).

Lemma verify_class_sound : forall class,
  verify_class class = true -> class_verified class.
intros class CODE.
apply mk_class_verified. intros mn md method H.
unfold verify_class in CODE. 
replace md with (snd (mn,md));[idtac|reflexivity]. pattern (mn,md), method.
apply (C.MethodList.check_all_correct (C.class_methods class)
        (fun d method => if C.method_static method then verify_static_method class method (snd d) else verify_instance_method class method (snd d))); auto.
 intros. destruct (C.method_static o); split; intros; try discriminate; auto.
Save.

End MkVerifier.

End MkPreVerifier.


















Require Import BasicMachineTypes.
Require Execution.
Require Import Store.
Require Import Arith.
Require Import OptionMonad.
Require Import OptionExt.
Require Import Compare_dec.
Require Import DestructExt.
Require Import Min.
Require Import Max.
Require Import List.
Require Import ListExt.
Require Omega.

Axiom cheat:False. Ltac cheat:=elimtype False; apply cheat.

Module MkFiniteMultiSet (Key : NAMETYPE).

Module NatTy.
Definition t:=nat.
End NatTy.

Module S := MkStore Key NatTy.

Definition t := S.t.

Definition mem : t -> Key.t -> nat :=
  fun mset e =>
  match S.lookup mset e with
  | None => 0
  | Some n => S n
  end.

Definition empty := S.empty.

Definition add_n : t -> Key.t -> nat -> t :=
  fun a k n =>
  match n with
  | O => a
  | S n => match S.lookup a k with
           | None => S.update a k n
           | Some x => S.update a k (S (n + x))
           end
  end.

Definition intersect : t -> t -> t := fun a b =>
  S.fold a (fun k n x => match S.lookup b k with None => x | Some n' => S.update x k (min n n') end) empty.

Definition union : t -> t -> t := fun a b =>
  S.fold a (fun k n x => match S.lookup x k with None => S.update x k n | Some n' => S.update x k (max n n') end) b.

Definition plus : t -> t -> t := fun a b =>
  S.fold a (fun k n x => match S.lookup x k with None => S.update x k n | Some n' => S.update x k (S (n + n')) end) b.

Definition add : t -> Key.t -> t := fun a k =>
  add_n a k 1.

Definition implies : t -> t -> Prop := fun a b =>
  forall k n,
    S.lookup b k = Some n ->
    exists n', S.lookup a k = Some n' /\ n <= n'.

Lemma implies_refl : forall a, implies a a.
intros. unfold implies. intros.
exists n. split; auto with arith.
Save.

Lemma implies_trans : forall a b c, implies a b -> implies b c -> implies a c.
unfold implies. intros.
destruct (H0 _ _ H1). destruct H2.
destruct (H _ _ H2). destruct H4. 
exists x0. split. assumption. omega.
Save.

Definition minus : t -> Key.t -> t :=
  fun a k =>
  match S.lookup a k with
  | None => a
  | Some O => S.remove k a
  | Some (S n) => S.update a k n
  end.

Definition eq := S.store_eq.
Definition eq_refl := S.store_eq_refl.
Definition eq_symm := S.store_eq_symm.
Definition eq_trans := S.store_eq_trans.

Lemma add_comm : forall a x1 x2, eq (add (add a x1) x2) (add (add a x2) x1).
unfold add. unfold add_n. intros. 
destruct (Key.eq_dec x1 x2).
 subst. apply eq_refl.
 destruct (option_dec (S.lookup a x1)). 
  destruct H. rewrite H. rewrite S.indep_lookup. 
   destruct (option_dec (S.lookup a x2)).
    destruct H0. rewrite H0. rewrite S.indep_lookup. 
     rewrite H. apply S.indep_update. assumption.
     unfold not. intro. apply n. symmetry. assumption.
    rewrite H0. rewrite S.indep_lookup. 
     rewrite H. apply S.indep_update. assumption.
     unfold not. intro. apply n. symmetry. assumption.
   assumption.
  rewrite H. rewrite S.indep_lookup.
   destruct (option_dec (S.lookup a x2)).
    destruct H0. rewrite H0. rewrite S.indep_lookup.
     rewrite H. apply S.indep_update. assumption.
     unfold not. intro. apply n. symmetry. assumption.
    rewrite H0. rewrite S.indep_lookup.
     rewrite H. apply S.indep_update. assumption.
     unfold not. intro. apply n. symmetry. assumption.
   assumption.
Save. 

Lemma add_cong : forall a b x, eq a b -> eq (add a x) (add b x).
unfold add. unfold add_n. unfold eq. 
intros. destruct (option_dec (S.lookup a x)). 
 destruct H0. rewrite H0. 
 destruct (H x x0). 
 destruct (option_dec (S.lookup b x)).
  destruct H3. rewrite H3. 
   rewrite (H1 H0) in H3. inversion H3. subst. apply S.store_eq_update_cong. assumption.
  rewrite (H1 H0) in H3. discriminate.
 rewrite H0. destruct (option_dec (S.lookup b x)).
  destruct H1. destruct (H x x0). rewrite (H3 H1) in H0. discriminate.
  rewrite H1. apply S.store_eq_update_cong. assumption.
Save.

Lemma add_minus : forall a b x, implies a (add b x) -> implies (minus a x) b.
unfold implies. unfold minus. unfold add. unfold add_n. simpl. intros. 
destruct_opt (S.lookup b x) H1 H.
 destruct (H x (S x0)).
  rewrite S.lookup_update. reflexivity.
 destruct H2. rewrite H2. destruct x1.
  elimtype False. omega.
  destruct (Key.eq_dec x k).
   subst. rewrite H0 in H1. inversion H1. subst.
   rewrite S.lookup_update. exists x1. split. reflexivity. omega.
   rewrite S.indep_lookup. 
    apply (H k n). rewrite S.indep_lookup; assumption.
    assumption.
 destruct (Key.eq_dec x k).
  subst. rewrite H0 in H1. discriminate.
  destruct (H x 0). rewrite S.lookup_update. reflexivity.
  destruct H2. rewrite H2.
  destruct (H k n). rewrite S.indep_lookup; assumption.
  destruct H4. 
  exists x1. split.
   destruct x0.
    apply S.remove_lookup_4; assumption.
    rewrite S.indep_lookup; assumption. 
   assumption.
Save.
   
(*
Lemma plus_comm : forall a b, plus a b = plus b a.
unfold plus. induction a; intros; simpl.
 induction b; simpl.
  reflexivity.
  destruct a. 
  destruct (S.lookup_informative (S.fold b (fun k0 n x => match S.lookup x k0 with Some n' => S.update x k0 (S (n+n')) | None => S.update x k0 n end) nil) k).
   destruct s. rewrite e.
   rewrite <- IHb.
*)
(*
Lemma aux : forall t0 x b a0,
 S.lookup b t0 = Some 0 ->
eq  (S.fold ((t0, S x) :: a0)
     (fun (k : S.key) (n : S.object) (x0 : S.t) =>
      match S.lookup x0 k with
      | Some n' => S.update x0 k (S (n + n'))
      | None => S.update x0 k n
      end) (S.remove t0 b))
 (S.fold ((t0, x) :: a0)
     (fun (k : S.key) (n : S.object) (x0 : S.t) =>
      match S.lookup x0 k with
      | Some n' => S.update x0 k (S (n + n'))
      | None => S.update x0 k n
      end) b).
intros. fold add. simpl. generalize x. clear x. induction a0; intros.
 simpl. rewrite S.remove_lookup. rewrite H. replace (x+0) with x. apply S.remove_update. omega.
 simpl. destruct a. 
 match goal with |- eq (match ?x with Some _ => _ | None => _ end) _ => destruct (option_dec x) end.
  destruct H0. rewrite H0. 
  match goal with |- eq _ (match ?x with Some _ => _ | None => _ end) => destruct (option_dec x) end.
   destruct H1. rewrite H1. 
  

*)

Lemma plus_add_minus : forall a b t n, S.lookup b t = Some n -> eq (plus (add a t) (minus b t)) (plus a b).
cheat.
Save.
(*
intros. unfold plus. unfold add. unfold minus. unfold add_n. 
rewrite H.
induction a. 
 simpl. destruct n. 
  rewrite S.remove_lookup. unfold eq. unfold S.store_eq. 
  intros. destruct (Key.eq_dec t0 k). 
   

destruct (option_dec (S.lookup a t0)). 
 destruct H0. rewrite H0. change (0+x) with x. induction a.
  discriminate.
  destruct a. destruct (Key.eq_dec k t0). 
   subst. rewrite S.lookup_cons in H0. inversion H0. subst.
   rewrite S.update_cons. change (0+x) with x. destruct n.
   unfold S.fold. fold S.fold. 
 
  simpl. destruct n.
   rewrite S.remove_lookup. unfold eq. unfold S.store_eq.
   intros. destruct (Key.eq_dec t0 k).
    subst. rewrite S.lookup_update. split; intros.
     inversion H0. assumption.
     rewrite <- H. assumption.
    rewrite S.indep_lookup. 
     split; intros.
      eapply S.remove_lookup_3. apply H0.
      apply S.remove_lookup_4. apply H0. assumption.
     assumption.
  rewrite S.lookup_update. rewrite S.update_update. unfold eq. unfold S.store_eq. intros. 
  destruct (Key.eq_dec t0 k). 
   subst. rewrite S.lookup_update. split; intros. 
    inversion H0. assumption.
    rewrite <- H. assumption.
   rewrite S.indep_lookup. auto. assumption.
 destruct a. destruct (Key.eq_dec k t0).
  subst. rewrite lookup_cons. rewrite update_cons. 
*)

Lemma plus_implies : forall b a1 a2, implies a1 a2 -> implies (plus b a1) (plus b a2).
unfold implies. unfold plus. induction b; intros; simpl in *.
 auto.
 destruct a. 
 destruct (S.lookup_informative (S.fold b (fun k n x => match S.lookup x k with Some n' => S.update x k (S (n+n')) | None => S.update x k n end) a2) k0).
  destruct s. rewrite e in H0. 
  destruct (IHb _ _ H _ _ e). destruct H1. rewrite H1. 
  destruct (Key.eq_dec k0 k). 
   subst. rewrite S.lookup_update in H0. rewrite S.lookup_update. inversion H0. subst. exists (S (o+x0)). split. reflexivity. omega.
   rewrite S.indep_lookup in H0. rewrite S.indep_lookup. 
    apply (IHb _ _ H _ _ H0). 
    assumption. assumption.
  rewrite e in H0. 
  destruct (S.lookup_informative (S.fold b (fun k n x => match S.lookup x k with Some n' => S.update x k (S (n+n')) | None => S.update x k n end) a1) k0).
   destruct s. rewrite e0. 
   destruct (Key.eq_dec k0 k). 
    subst. rewrite S.lookup_update in H0. rewrite S.lookup_update. inversion H0. subst. exists (S (n+x)). split. reflexivity. omega.
    rewrite S.indep_lookup in H0. rewrite S.indep_lookup. 
     apply (IHb _ _ H _ _ H0).
     assumption. assumption.
   rewrite e0. destruct (Key.eq_dec k0 k).
    subst. rewrite S.lookup_update. rewrite S.lookup_update in H0. inversion H0. subst. exists n. split. reflexivity. omega.
    rewrite S.indep_lookup. rewrite S.indep_lookup in H0. 
     apply (IHb _ _ H _ _ H0).
     assumption. assumption.
Save.

Lemma implies_eq : forall a b b', eq b b' -> implies a b -> implies a b'.
unfold eq. unfold implies. unfold S.store_eq.
intros. destruct (H k n). apply (H0 _ _ (H3 H1)). 
Save.

Definition implies_dec : t -> t -> bool := fun a b =>
  S.check_all b (fun k n => 
                  match S.lookup a k with
                 | None => false
                 | Some n' =>
                    match le_lt_dec n n' with
                    | left _ => true
                    | right _ => false
                    end
                 end).

Lemma implies_dec_sound : forall a b, implies_dec a b = true -> implies a b.
unfold implies_dec. unfold implies. intros a b H k n H0. 
match goal with [ _:(S.check_all ?s ?f) = _ |- _ ] =>
  apply (S.check_all_correct s f (fun k n => exists n', S.lookup a k = Some n' /\ n <= n')); try assumption end.
intros. destruct_opt (S.lookup a k0) H2 H1.
exists x. destruct (le_lt_dec o x).
 auto. 
 discriminate.
Save.
Implicit Arguments implies_dec_sound [a b].

Lemma union_p1 : forall a b, implies (union a b) a.
unfold implies. unfold union. intros a b. 
induction a; simpl in *; intros.
 discriminate.
 destruct a. destruct (Key.eq_dec k k0).
  inversion H. subst. 
  destruct (S.lookup_informative (S.fold a0 (fun k n x => match S.lookup x k with Some n' => S.update x k (max n n') | None => S.update x k n end) b) k0).
   destruct s. rewrite e. rewrite S.lookup_update. exists (max n x). split. reflexivity. apply le_max_l.
   rewrite e. rewrite S.lookup_update. exists n. split. reflexivity. auto with arith.
  destruct (IHa _ _ H). destruct H0.
  destruct (S.lookup_informative (S.fold a0 (fun k n x => match S.lookup x k with Some n' => S.update x k (max n n') | None => S.update x k n end) b) k0).
   destruct s. rewrite e. rewrite S.indep_lookup.
    exists x. auto.
    unfold not. intros. apply n0. symmetry. assumption.
   rewrite e. rewrite S.indep_lookup.
    exists x. auto.
    unfold not. intros. apply n0. symmetry. assumption.
Save.

Lemma union_p2 : forall a b, implies (union a b) b.
unfold implies. unfold union. intros a b. 
induction a; simpl; intros.
 exists n. auto with arith. 
 destruct a. destruct (Key.eq_dec k0 k).
  subst. destruct (IHa _ _ H). destruct H0. rewrite H0. rewrite S.lookup_update. exists (max o x). split. 
   reflexivity. 
   pose (le_max_r o x). omega.
  destruct (S.lookup_informative (S.fold a0 (fun k1 n1 x => match S.lookup x k1 with Some n'0 => S.update x k1 (max n1 n'0) | None => S.update x k1 n1 end) b) k0).
   destruct s. rewrite e. rewrite S.indep_lookup; auto.
   rewrite e. rewrite S.indep_lookup; auto.
Save.

(*Lemma union_pair : forall a b c,
  implies c a -> implies c b -> implies c (union a b).*)

End MkFiniteMultiSet.

Module MemVerifier (B : BASICS).

Module E := Execution.Execution B.

Module Assertion := MkFiniteMultiSet B.Classname.

Module NatKey.
Definition t := nat.
Definition eq_dec := eq_nat_dec.
End NatKey.
Module Cert := Store.MkStore NatKey Assertion.

Definition cert_incl := fun c1 c2 => forall n, option_incl (Cert.lookup c1 n) (Cert.lookup c2 n).

Lemma cert_incl_refl : forall c, cert_incl c c.
unfold cert_incl. intros. apply option_incl_refl.
Save.

Lemma cert_incl_trans : forall c1 c2 c3, cert_incl c1 c2 -> cert_incl c2 c3 -> cert_incl c1 c3.
unfold cert_incl. intros. 
eapply option_incl_trans. apply H. apply H0.
Save.

Lemma cert_incl_update : forall c n a, Cert.lookup c n = None -> cert_incl c (Cert.update c n a).
unfold cert_incl. intros.
destruct (eq_nat_dec n n0). 
subst n. rewrite H. rewrite Cert.lookup_update. apply o_inc_2.
rewrite Cert.indep_lookup. apply option_incl_refl. assumption.
Save.

Lemma cert_incl_lookup : forall c1 c2 n a, Cert.lookup c1 n = Some a -> cert_incl c1 c2 -> Cert.lookup c2 n = Some a.
intros. unfold cert_incl in H0. 
set (H1:=H0 n). rewrite H in H1. inversion H1. trivial.
Save.

Section CodeVerifier.

Hypothesis class : E.R.C.class.
Hypothesis code : E.R.C.code.

Definition two_way_branch_helper := fun cert pc offset =>
  target <- E.R.C.I.pc_plus_offset pc offset;:
  a1 <- Cert.lookup cert (S pc);:
  a2 <- Cert.lookup cert target;:
  ret (Assertion.union a1 a2).

Definition wp : Cert.t -> nat -> E.R.C.I.opcode -> option Assertion.t :=
  fun cert pc op =>
  match op with
  (* Arithmetic *)
  | E.R.C.I.op_iarithb _ => Cert.lookup cert (S pc) (* FIXME: may throw an exception *)
  | E.R.C.I.op_iarithu _ => Cert.lookup cert (S pc)
  | E.R.C.I.op_iinc _ _  => Cert.lookup cert (S pc)

  (* Stack operations *)
  | E.R.C.I.op_dup       => Cert.lookup cert (S pc)
  | E.R.C.I.op_dup_x1    => Cert.lookup cert (S pc)
  | E.R.C.I.op_dup_x2    => Cert.lookup cert (S pc)
  | E.R.C.I.op_dup2      => Cert.lookup cert (S pc)
  | E.R.C.I.op_dup2_x1   => Cert.lookup cert (S pc)
  | E.R.C.I.op_dup2_x2   => Cert.lookup cert (S pc)
  | E.R.C.I.op_nop       => Cert.lookup cert (S pc)
  | E.R.C.I.op_pop       => Cert.lookup cert (S pc)
  | E.R.C.I.op_pop2      => Cert.lookup cert (S pc)
  | E.R.C.I.op_swap      => Cert.lookup cert (S pc)

  (* Local Variables *)
  | E.R.C.I.op_load _ _  => Cert.lookup cert (S pc)
  | E.R.C.I.op_store _ _ => Cert.lookup cert (S pc)

  (* OO *)
  (*| E.R.C.I.op_instanceof _  => Cert.lookup cert (S pc) *)
  | E.R.C.I.op_aconst_null   => Cert.lookup cert (S pc)
  | E.R.C.I.op_getstatic _   => Cert.lookup cert (S pc)
  | E.R.C.I.op_new idx       =>
     a <- Cert.lookup cert (S pc);:
     ref <- E.R.C.ConstantPool.lookup (E.R.C.class_constantpool class) idx;:
     match ref with
     | E.R.C.cpe_classref cls_nm =>
        ret (Assertion.add a cls_nm)
     | _ => fail
     end
  | E.R.C.I.op_putstatic _   => Cert.lookup cert (S pc)

  (* Comparisons and control flow *)
  | E.R.C.I.op_if_acmp _ offset => two_way_branch_helper cert pc offset
  | E.R.C.I.op_if_icmp _ offset => two_way_branch_helper cert pc offset
  | E.R.C.I.op_if _ offset      => two_way_branch_helper cert pc offset
  | E.R.C.I.op_ifnonnull offset => two_way_branch_helper cert pc offset
  | E.R.C.I.op_ifnull offset    => two_way_branch_helper cert pc offset
  | E.R.C.I.op_goto offset         => 
     new_pc <- E.R.C.I.pc_plus_offset pc offset;:
     Cert.lookup cert new_pc
  | E.R.C.I.op_valreturn _      => ret Assertion.empty
  | E.R.C.I.op_return           => ret Assertion.empty
  | E.R.C.I.op_athrow           => fail
  | E.R.C.I.op_dcmp _           => Cert.lookup cert (S pc)
  | E.R.C.I.op_fcmp _           => Cert.lookup cert (S pc)
  | E.R.C.I.op_lcmp             => Cert.lookup cert (S pc)
  | E.R.C.I.op_lookupswitch _ _ _ => fail
  | E.R.C.I.op_tableswitch _ _ _ _ => fail

  (* Arrays not done yet *)

  (* Constants *)
  | E.R.C.I.op_iconst _        => Cert.lookup cert (S pc)
  | E.R.C.I.op_dconst _        => Cert.lookup cert (S pc)
  | E.R.C.I.op_fconst _        => Cert.lookup cert (S pc)
  | E.R.C.I.op_lconst _        => Cert.lookup cert (S pc)
  | E.R.C.I.op_ldc _           => Cert.lookup cert (S pc)
  | E.R.C.I.op_ldc2 _          => Cert.lookup cert (S pc)

  (* Concurrency *)

  (* Conversions *)

  | _ => fail
  end.

Inductive safe_instruction : Cert.t -> nat -> E.R.C.I.opcode -> Prop :=
  mk_safe_instruction : forall cert pc op a1 a2,
    Cert.lookup cert pc = Some a1 ->
    wp cert pc op = Some a2 ->
    Assertion.implies a1 a2 ->
    safe_instruction cert pc op.

Inductive safe_code : Cert.t -> Prop :=
  mk_safe_code : forall cert,
    (forall n a, Cert.lookup cert n = Some a -> n < length (E.R.C.code_code code)) ->
    (forall n op, nth_error (E.R.C.code_code code) n = Some op -> safe_instruction cert n op) ->
    safe_code cert.

Definition completion_step : Cert.t -> nat -> E.R.C.I.opcode -> option Cert.t :=
  fun cert pc op =>
  a <- wp cert pc op;:
  match Cert.lookup cert pc with
  | None    => ret (Cert.update cert pc a)
  | Some a' => if Assertion.implies_dec a' a then ret cert else fail
  end.

Fixpoint complete_cert_aux (ops:list E.R.C.I.opcode) (cert:Cert.t) (pc:nat) {struct ops} : option Cert.t :=
  match ops with
  | nil     => None
  | op::nil => completion_step cert pc op 
  | op::ops => cert' <- complete_cert_aux ops cert (S pc);: completion_step cert' pc op
  end.

Fixpoint clean_cert (cert:Cert.t) (limit:nat) {struct cert} : Cert.t :=
  match cert with
  | nil         => nil
  | (n,a)::cert =>
     match le_lt_dec limit n with
     | left _ => (* limit <= n *) clean_cert cert limit
     | right _ => (* n < limit *) (n,a)::clean_cert cert limit
     end
  end.

Definition complete_cert : Cert.t -> option Cert.t :=
  fun cert =>
    complete_cert_aux (E.R.C.code_code code) (clean_cert cert (length (E.R.C.code_code code))) 0.

Lemma clean_ok : forall cert limit n, n >= limit -> Cert.lookup (clean_cert cert limit) n = None.
intros. generalize n H. clear n H.
induction cert; intros.
trivial. 
simpl. destruct a. 
destruct (le_lt_dec limit k). apply IHcert. apply H.
simpl. rewrite (IHcert n H). destruct (NatKey.eq_dec n k). elimtype False. omega. trivial.
Save.

Lemma clean_contra : forall c limit, (forall n, n >= limit -> Cert.lookup c n = None) ->
  (forall n x, Cert.lookup c n = Some x -> n < limit).
intros. 
destruct (dec_lt n limit). assumption.
assert (n >= limit). omega. rewrite (H n H2) in H0. discriminate.
Save.

Lemma step_incl : forall c c' n op, completion_step c n op = Some c' -> cert_incl c c'.
intros. unfold completion_step in H.
destruct (wp c n op); try discriminate.
destruct_opt (Cert.lookup c n) H0 H; simpl in H. 
 destruct (Assertion.implies_dec x t). 
  inversion H. apply cert_incl_refl.
  discriminate.
 inversion H. apply cert_incl_update. assumption.
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
  (forall n, n >= limit -> Cert.lookup c n = None) ->
  (forall n, n >= limit -> Cert.lookup c' n = None).
intros.
unfold completion_step in H0. 
destruct (wp c pc op); try discriminate. 
destruct (Cert.lookup c pc). 
 simpl in H0. destruct (Assertion.implies_dec o t). 
  inversion H0. subst. auto.
  discriminate.
 simpl in H0. inversion H0. subst. rewrite Cert.indep_lookup.
  auto.
  omega.
Save.

Lemma complete_cert_aux_clean : forall c c' n ops, 
  (forall m, m >= n+length ops -> Cert.lookup c m = None) ->
  complete_cert_aux ops c n = Some c' -> 
  (forall m, m >= n+length ops -> Cert.lookup c' m = None).
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

Lemma cert_incl_wp : forall c1 c2 n op a, wp c1 n op = Some a -> cert_incl c1 c2 -> wp c2 n op = Some a.
intros.
destruct op; simpl in * |- *; unfold two_way_branch_helper in *;
 first [ discriminate
       | assumption
       | try (destruct i; try discriminate; simpl);
         destruct_opt (Cert.lookup c1 (S n)) H1 H; rewrite (cert_incl_lookup c1 c2 (S n) x H1 H0); apply H
       | destruct_opt (E.R.C.I.pc_plus_offset n z) H1 H; rewrite H1; 
         destruct_opt (Cert.lookup c1 (S n)) H2 H; rewrite (cert_incl_lookup c1 c2 (S n) x0 H2 H0); simpl in * |- *;
         destruct_opt (Cert.lookup c1 x) H3 H; rewrite (cert_incl_lookup c1 c2 x x1 H3 H0); simpl in * |- *;
         apply H
       | destruct_opt (E.R.C.I.pc_plus_offset n z) H1 H; rewrite H1; simpl in * |- *; eapply cert_incl_lookup; [apply H|apply H0]
       | idtac ].
Save.

Lemma cert_update_wp : forall c n op a,
     Cert.lookup c n = None -> wp c n op = Some a -> wp (Cert.update c n a) n op = Some a.
intros. eapply cert_incl_wp. apply H0. apply cert_incl_update. apply H.
Save.

Lemma step_ok : forall c c' op pc, completion_step c pc op = Some c' -> safe_instruction c' pc op.
intros. unfold completion_step in H.
destruct_opt (wp c pc op) H0 H. 
destruct_opt (Cert.lookup c pc) H1 H; simpl in H. 
 destruct_bool (Assertion.implies_dec x0 x) H2 H.
 inversion H. subst. eapply mk_safe_instruction; eauto.
  apply Assertion.implies_dec_sound. assumption.
 inversion H. subst. eapply mk_safe_instruction.
  apply Cert.lookup_update. apply cert_update_wp; assumption.
  apply Assertion.implies_refl.
Save.

Lemma cert_incl_safe : forall c1 c2 pc op,
   safe_instruction c1 pc op -> cert_incl c1 c2 -> safe_instruction c2 pc op.
intros.
inversion H. 
eapply mk_safe_instruction. 
  eapply cert_incl_lookup. apply H1. apply H0.
  eapply cert_incl_wp. apply H2. apply H0.
  assumption.
Save.

Lemma complete_cert_ok : forall c c', complete_cert c = Some c' -> safe_code c'.
intros. unfold complete_cert in H.
eapply mk_safe_code. 
apply clean_contra. intros. 
apply (complete_cert_aux_clean (clean_cert c (length (E.R.C.code_code code))) c' 0 (E.R.C.code_code code)). 
intros. apply clean_ok. assumption. apply H. simpl. assumption.
intros. 
destruct (complete_cert_aux_prop n (E.R.C.code_code code) _ c' (nth_error_length_2 _ _ _ _ H0) H). destruct H1. destruct H2.
destruct (tail_nth_error n (E.R.C.code_code code) op H0).
rewrite H4 in H1. simpl in H1. 
destruct x0. 
eapply cert_incl_safe. eapply step_ok. apply H1. apply H3.
destruct_opt (complete_cert_aux (o::x0) (clean_cert c (length (E.R.C.code_code code))) (S n)) H5 H1. 
simpl in H1. eapply cert_incl_safe. eapply step_ok. apply H1. apply H3. 
Save.

End CodeVerifier.

Definition count_object_heap : E.ObjectHeap.t -> Assertion.t :=
  fun heap =>
    E.ObjectHeap.fold heap (fun k _ _ a => Assertion.add a k) Assertion.empty.

Lemma add_object_count : forall h t o h' addr,
  E.ObjectHeap.new h t o = (h', addr) ->
  Assertion.eq (Assertion.add (count_object_heap h) t) (count_object_heap h').
intros. 
destruct h. simpl in *.
inversion H. clear H H2. subst. 
unfold count_object_heap. unfold E.ObjectHeap.fold. simpl.
induction actual_heap. 
 apply Assertion.eq_refl.
 unfold E.ObjectHeap.S.fold at 1.
 destruct a. 
 eapply Assertion.eq_trans. 
  apply Assertion.add_comm. 
  eapply Assertion.eq_trans.
   apply Assertion.add_cong. apply IHactual_heap. 
    intros. eapply E.ObjectHeap.S.lookup_None. apply max_unallocated. assumption.
    destruct k. unfold E.ObjectHeap.S.update at 2. fold E.ObjectHeap.S.update.
    destruct (E.ObjectHeap.Key.eq_dec (t,max_addr) (t0, n)).
     simpl. inversion e. subst. elimtype False. 
      assert (Some o0 = None). 
       pose (max_unallocated t0 n). generalize e0. clear e0. intro. unfold E.ObjectHeap.S.lookup in e0. destruct (E.ObjectHeap.Key.eq_dec (t0, n) (t0, n)).
       apply e0. auto with arith.
       contradiction.
      discriminate.
     simpl. apply Assertion.eq_refl.
Save.

Lemma add_object_count_2 : forall a h b t o h' addr x,
  Assertion.S.lookup b t = Some x ->
  Assertion.implies a (Assertion.plus (count_object_heap h) b) ->
  E.ObjectHeap.new h t o = (h', addr) ->
  Assertion.implies a (Assertion.plus (count_object_heap h') (Assertion.minus b t)).
intros. refine (Assertion.implies_eq _ _ _ _ H0). 
 eapply Assertion.eq_trans. apply Assertion.eq_symm. eapply Assertion.plus_add_minus. apply H. 

Inductive safe_current_frame : E.R.cert_classpool -> E.frame -> Assertion.t -> Prop :=
| mk_safe_current_frame : forall classes op_stack lvars pc code class allowance required_allowance cert,
    E.R.C.Classpool.lookup (E.R.classpool classes) (E.R.C.class_name class) = Some class ->
    safe_code class code cert ->
    Cert.lookup cert pc = Some required_allowance ->
    Assertion.implies allowance required_allowance ->
    safe_current_frame classes (E.mkFrame op_stack lvars pc code class) allowance.

Inductive safe_state : E.R.C.Preclasspool.t -> E.state -> Assertion.t -> Prop :=
| mk_safe_state : forall f fs classes preclasses heap statics total_allowance current_allowance,
   safe_current_frame classes f current_allowance ->
   Assertion.implies total_allowance (Assertion.plus (count_object_heap heap) (current_allowance)) ->
   safe_state preclasses (E.mkState (f::fs) classes heap statics) total_allowance. 

Ltac go_wrong := right; right; right; assumption.
Ltac go_cont := match goal with E:E.cont ?s = _ |- _ => left; exists s; split; auto end.
Ltac easy_case := go_cont; 
 (eapply mk_safe_state;
 [eapply mk_safe_current_frame; eauto
 |eapply Assertion.implies_trans; [ eauto | apply Assertion.plus_implies; assumption ]]).
Ltac switch_option := match goal with E:match ?v with Some _ => _ | None => _ end = _ |- _ => destruct v; try go_wrong end.
Ltac switch_list := match goal with E:match ?v with _::_ => _ | nil => _ end = _ |- _ => destruct v; try go_wrong end.
Ltac switch_category := match goal with E:match ?v with E.R.C.category1 => _ | E.R.C.category2 => _ end = _ |- _ => destruct v; try go_wrong end.
Ltac switch_val := match goal with E:match ?v with E.rt_int _ => _ | E.rt_addr _ => _ | E.rt_long => _ | E.rt_double => _ | E.rt_float => _ end = _ |- _ => destruct v; try go_wrong end.
Ltac switch_bool := match goal with E:match ?v with true => _ | false => _ end = _ |- _ => destruct v; try go_wrong end.
Ltac switch_pair := match goal with E:match ?v with (_,_) => _ end = _ |- _ => destruct v end.
Ltac switch H := destruct H; try go_wrong.

Ltac case_auto := first [ easy_case | switch_option; case_auto | switch_list; case_auto | switch_category; case_auto | switch_val; case_auto | switch_bool; case_auto ].


Lemma elim_pair : forall (A B:Set) (p:A * B), exists a, exists b, p = (a,b).
intros. destruct p. exists a. exists b. reflexivity.
Save.



Lemma exec_safe : forall preclasses s allowance res,
  safe_state preclasses s allowance ->
  E.exec preclasses s = res ->
    (exists s', E.cont s' = res /\ safe_state preclasses s' allowance)
  \/(exists s', exists v, E.stop s' v = res /\ safe_state preclasses s' allowance)
  \/(exists s', exists e, E.stop_exn s' e = res /\ safe_state preclasses s' allowance)
  \/E.wrong = res.
intros preclasses s allowance res s_safe E.

inversion s_safe. subst s total_allowance. clear s_safe.
rename H0 into allowance_implication.
inversion H. subst preclasses0 allowance0 f classes0.
rename H0 into class_exists.
inversion H2. subst cert0. 
destruct (nth_error_ok _ (E.R.C.code_code code) _ (H0 _ _ H3)).
pose (safe_instr:=H1 _ _ H5). inversion safe_instr. subst cert0 pc0 x.
rewrite H3 in H6. inversion H6. subst a1. 
clear H H6 H3 H0 H1 safe_instr.
rename H2 into code_is_safe.
rename H4 into current_implies_required.
rename H5 into op_exists.
rename H7 into wp_code.
rename H8 into required_implies_wp_required.

simpl in E. rewrite op_exists in E. 
destruct op; try discriminate; simpl in *; try case_auto.

(* op_instanceof *)
(*switch_list. switch_val. switch_option. switch o0. 
switch (E.R.resolve_class (E.R.C.class_name class) t0 classes preclasses).
switch_option.
switch (E.R.C.Classpool.lookup_informative (E.R.classpool classes') (fst p0)).
switch s.
switch_bool; easy_case.*)

(* op_getstatic *)
switch_option. switch o. 
switch (E.R.resolve_field (E.R.C.class_name class) t0 t1 j classes preclasses).
 switch a. generalize E. clear E. case a0. intros.
 switch_bool.
  switch_option; easy_case.
  cheat. (* FIXME: do exceptions *)
 cheat.

(* op_new *)
destruct_opt (Cert.lookup cert (S pc)) H wp_code. simpl in wp_code.
switch_option. switch o. inversion wp_code. subst a2.
switch (E.R.resolve_class (E.R.C.class_name class) t0 classes preclasses).
 switch_bool.
  cheat.
  switch_bool. 
   cheat.
   destruct (elim_pair _ _ (E.ObjectHeap.new heap t0 E.FieldStore.empty)). destruct H0.
   rewrite H0 in E. 
   go_cont.
   eapply mk_safe_state. 
    eapply mk_safe_current_frame; eauto.
     apply Assertion.add_minus. apply required_implies_wp_required.      

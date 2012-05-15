Require Import List.
Require Import FSets.
Require FSetAVL.
Require Peano_dec.
Require Import Setoid.
Require Import OptionMonad.
Require Import OptionExt.
Require Import BoolExt.
Require Import ILLInterfaces.
Require Import ResourceAlgebra.
Require Import Arith.

Require Import BasicMachineTypes.

Module MkILLSyntax
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B)
  : ILL_SYNTAX B BASESYN.

Import BASESYN.

Definition context := list formula.

Inductive prf_term : Set :=
| t_lvar         : nat -> prf_term
| t_ivar         : nat -> prf_term
| t_i_intro      : prf_term
| t_tensor_intro : prf_term -> prf_term -> prf_term
| t_tensor_elim  : prf_term -> prf_term -> prf_term
| t_and_intro    : prf_term -> prf_term -> prf_term
| t_and_elim1    : prf_term -> prf_term
| t_and_elim2    : prf_term -> prf_term
| t_lolli_intro  : formula -> prf_term -> prf_term
| t_lolli_elim   : prf_term -> prf_term -> prf_term
| t_bang_intro   : prf_term -> prf_term
| t_bang_elim    : prf_term -> prf_term -> prf_term
| t_axiom        : axiom_name -> prf_term -> prf_term
| t_let          : prf_term -> prf_term -> prf_term.

Fixpoint l_shift (d c:nat) (t:prf_term) {struct t} : prf_term :=
 match t with
 | t_lvar k             => if le_lt_dec c k then t_lvar (d + k) else t_lvar k
 | t_ivar k             => t_ivar k
 | t_i_intro            => t_i_intro
 | t_tensor_intro t1 t2 => t_tensor_intro (l_shift d c t1) (l_shift d c t2)
 | t_tensor_elim t1 t2  => t_tensor_elim (l_shift d c t1) (l_shift d (S (S c)) t2)
 | t_and_intro t1 t2    => t_and_intro (l_shift d c t1) (l_shift d c t2)
 | t_and_elim1 t        => t_and_elim1 (l_shift d c t)
 | t_and_elim2 t        => t_and_elim2 (l_shift d c t)
 | t_lolli_intro A t    => t_lolli_intro A (l_shift d (S c) t)
 | t_lolli_elim t1 t2   => t_lolli_elim (l_shift d c t1) (l_shift d c t2)
 | t_bang_intro t       => t_bang_intro (l_shift d c t)
 | t_bang_elim t1 t2    => t_bang_elim (l_shift d c t1) (l_shift d c t2)
 | t_axiom nm t         => t_axiom nm (l_shift d c t)
 | t_let t1 t2          => t_let (l_shift d c t1) (l_shift d (S c) t2)
 end.

Definition var_subst : nat -> nat -> prf_term -> prf_term.
intros k j t'.
destruct (lt_eq_lt_dec k j) as [[k_lt_j | k_eq_j] | j_lt_k]. 
 exact (t_lvar k).
 exact t'.
 destruct (O_or_S k) as [[m k_eq_Sm] | k_eq_0]. 
  exact (t_lvar m).
  subst k. elimtype False. apply (lt_n_O j j_lt_k). 
Defined. 

Fixpoint l_subst (t:prf_term) (s:prf_term) (j:nat) {struct t} : prf_term :=
 match t with
 | t_lvar k             => var_subst k j s
 | t_ivar k             => t_ivar k
 | t_i_intro            => t_i_intro
 | t_tensor_intro t1 t2 => t_tensor_intro (l_subst t1 s j) (l_subst t2 s j)
 | t_tensor_elim t1 t2  => t_tensor_elim (l_subst t1 s j) (l_subst t2 (l_shift 2 0 s) (S (S j)))
 | t_and_intro t1 t2    => t_and_intro (l_subst t1 s j) (l_subst t2 s j)
 | t_and_elim1 t        => t_and_elim1 (l_subst t s j)
 | t_and_elim2 t        => t_and_elim2 (l_subst t s j)
 | t_lolli_intro A t    => t_lolli_intro A (l_subst t (l_shift 1 0 s) (S j))
 | t_lolli_elim t1 t2   => t_lolli_elim (l_subst t1 s j) (l_subst t2 s j)
 | t_bang_intro t       => t_bang_intro (l_subst t s j)
 | t_bang_elim t1 t2    => t_bang_elim (l_subst t1 s j) (l_subst t2 s j)
 | t_axiom nm t         => t_axiom nm (l_subst t s j)
 | t_let t1 t2          => t_let (l_subst t1 s j) (l_subst t2 (l_shift 1 0 s) (S j))
 end.

Module VarSet : FSetInterface.S with Module E := Nat_as_OT := FSetAVL.Make Nat_as_OT.

Definition shift_step n s := match n with O => s | S n => VarSet.add n s end.
Definition shift_down s := VarSet.fold shift_step s VarSet.empty.

Definition shift2_step d c n s := if le_lt_dec c n then VarSet.add (d+n) s else VarSet.add n s.
Definition shift_varset d c s := VarSet.fold (shift2_step d c) s VarSet.empty.

Inductive prf : context -> context -> prf_term -> formula -> VarSet.t -> Prop :=
| prf_ivar : forall Gi G n A U,
   nth_error Gi n = Some A ->
   VarSet.Equal U VarSet.empty ->
   prf Gi G (t_ivar n) A U
| prf_lvar : forall Gi G n A U,
   nth_error G n = Some A ->
   VarSet.Equal U (VarSet.singleton n) ->
   prf Gi G (t_lvar n) A U
| prf_i_intro : forall Gi G U,
   VarSet.Equal U VarSet.empty ->
   prf Gi G t_i_intro f_i U
| prf_tensor_intro : forall Gi G t1 t2 A B U1 U2 U,
   prf Gi G t1 A U1 ->
   prf Gi G t2 B U2 ->
   VarSet.Empty (VarSet.inter U1 U2) ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_tensor_intro t1 t2) (f_tensor A B) U
| prf_tensor_elim : forall Gi G t1 t2 A B C U1 U2 U,
   prf Gi G t1 (f_tensor A B) U1 ->
   prf Gi (A::B::G) t2 C U2 ->
   VarSet.Empty (VarSet.inter U1 (shift_down (shift_down U2))) ->
   VarSet.Equal U (VarSet.union U1 (shift_down (shift_down U2))) ->
   prf Gi G (t_tensor_elim t1 t2) C U
| prf_and_intro : forall Gi G t1 t2 A B U1 U2 U,
   prf Gi G t1 A U1->
   prf Gi G t2 B U2 ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_and_intro t1 t2) (f_and A B) U
| prf_and_elim1 : forall Gi G t A B U,
   prf Gi G t (f_and A B) U ->
   prf Gi G (t_and_elim1 t) A U
| prf_and_elim2 : forall Gi G t A B U,
   prf Gi G t (f_and A B) U ->
   prf Gi G (t_and_elim2 t) B U
| prf_lolli_intro : forall Gi G t A B Ut U,
   prf Gi (A::G) t B Ut ->
   VarSet.Equal U (shift_down Ut) ->
   prf Gi G (t_lolli_intro A t) (f_lolli A B) U
| prf_lolli_elim : forall Gi G t1 t2 A B U1 U2 U,
   prf Gi G t1 (f_lolli A B) U1 ->
   prf Gi G t2 A U2 ->
   VarSet.Empty (VarSet.inter U1 U2) ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_lolli_elim t1 t2) B U
| prf_bang_intro : forall Gi G t A U,
   prf Gi G t A U ->
   VarSet.Empty U ->
   prf Gi G (t_bang_intro t) (f_bang A) U
| prf_bang_elim : forall Gi G t1 t2 A B U1 U2 U,
   prf Gi G t1 (f_bang A) U1 ->
   prf (A::Gi) G t2 B U2 ->
   VarSet.Empty (VarSet.inter U1 U2) ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_bang_elim t1 t2) B U
| prf_axiom : forall Gi G t ax U,
   prf Gi G t (axiom_domain ax) U ->
   prf Gi G (t_axiom ax t) (axiom_codomain ax) U
| prf_let : forall Gi G t1 t2 A B U1 Ut2 U2 U,
   prf Gi G t1 A U1 ->
   prf Gi (A::G) t2 B Ut2 ->
   VarSet.Equal U2 (shift_down Ut2) ->
   VarSet.Empty (VarSet.inter U1 U2) ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_let t1 t2) B U.

Module VarSetProps := Properties VarSet.

Lemma varset_setoid : Setoid_Theory VarSet.t VarSet.Equal.
Proof.
 constructor. unfold Reflexive. reflexivity. unfold Symmetric. symmetry. assumption. intros. unfold Transitive. apply VarSet.eq_trans.
Qed.

Lemma prf_mor_aux : forall Gi G t A U1 U2, VarSet.Equal U1 U2 -> prf Gi G t A U1 -> prf Gi G t A U2.
intros.
generalize U2 H. clear U2 H.
induction H0; intros U2' U2'_eq_U; econstructor; eauto; rewrite <- U2'_eq_U; assumption.
Save.

Add Morphism prf with signature (@eq context) ==> (@eq context) ==> (@eq prf_term) ==> (@eq formula) ==> VarSet.Equal ==> iff as prf_mor.
intuition eauto using prf_mor_aux, VarSetProps.equal_sym.
Save.

Add Morphism shift2_step with signature (@eq nat) ==> (@eq nat) ==> (@eq nat) ==> VarSet.Equal ==> VarSet.Equal as shift2_step_mor.
unfold shift2_step. intros. destruct (le_lt_dec y0 y1); rewrite H; reflexivity.
Save.

Add Morphism shift_varset with signature (@eq nat) ==> (@eq nat) ==> VarSet.Equal ==> VarSet.Equal as shift_varset_mor.
unfold shift_varset. intros. refine (VarSetProps.fold_equal varset_setoid _ _ _ H).
 unfold compat_op. intros. unfold VarSet.E.eq in H0. subst x'. apply shift2_step_mor; try reflexivity. assumption.
 unfold transpose. intros. unfold shift2_step.
 destruct (le_lt_dec y0 x0); destruct (le_lt_dec y0 y2); rewrite VarSetProps.add_add; reflexivity.
Save.

Add Morphism shift_down with signature VarSet.Equal ==> VarSet.Equal as shift_down_mor.
unfold shift_down. intros. refine (VarSetProps.fold_equal varset_setoid _ _ _ H).
 unfold compat_op. unfold shift_step. intros. destruct x0; destruct x'.
  assumption.
  discriminate.
  discriminate. 
  inversion H0. rewrite H1. reflexivity.
 unfold transpose. intros. unfold shift_step.
 destruct x0; destruct y0; try reflexivity; eauto using VarSetProps.add_add.
Save.

Lemma list_empty : forall l,
 (forall x, ~InA (@eq nat) x l) -> l = nil.
destruct l; intros.
 reflexivity.
 elimtype False. apply (H n). constructor. reflexivity.
Save.

Lemma elements_empty : VarSet.elements VarSet.empty = nil.
apply list_empty. intros. unfold not. intro. refine (VarSet.empty_1 _). apply VarSet.elements_2. apply H.
Save. 

Lemma shift_varset_empty : forall d c,
 VarSet.Equal (shift_varset d c VarSet.empty) VarSet.empty.
intros. unfold shift_varset. rewrite VarSet.fold_1. rewrite elements_empty. reflexivity.
Save.

Lemma list_single : forall l y,
 (forall x, InA (@eq nat) x l <-> x=y) ->
 sort Nat_as_OT.lt l ->
 l = y::nil.
destruct l; intros.
 assert (InA (@eq nat) y nil). rewrite H. reflexivity. inversion H1.
 assert (n = y). rewrite <- H. constructor. reflexivity.
 subst. destruct l.
  reflexivity.
  assert (n = y). rewrite <- H. right. constructor. reflexivity.
  subst. inversion H0. inversion H4. elimtype False. refine (Nat_as_OT.lt_not_eq _ _ H6 _). unfold Nat_as_OT.eq. reflexivity.
Save. 

Lemma elements_singleton : forall n, VarSet.elements (VarSet.singleton n) = n::nil.
intros. apply list_single.
 intros. split; intro.
  symmetry. eapply VarSet.singleton_1. apply VarSet.elements_2. assumption.
  apply VarSet.elements_1. apply VarSet.singleton_2. unfold VarSet.E.eq. symmetry. assumption.
 apply VarSet.elements_3.
Save.

Lemma shift_varset_singleton : forall d c n,
 c <= n ->
 VarSet.Equal (shift_varset d c (VarSet.singleton n)) (VarSet.singleton (d + n)).
intros. unfold shift_varset. rewrite VarSet.fold_1. rewrite elements_singleton. simpl. unfold shift2_step. 
destruct (le_lt_dec c n).
 auto with set.
 elimtype False. omega.
Save.

Lemma shift_varset_singleton2 : forall d c n,
 n < c ->
 VarSet.Equal (shift_varset d c (VarSet.singleton n)) (VarSet.singleton n).
intros. unfold shift_varset. rewrite VarSet.fold_1. rewrite elements_singleton. simpl. unfold shift2_step. 
destruct (le_lt_dec c n).
 elimtype False. omega.
 auto with set.
Save.

Lemma lookup_length : forall (A:Set) (G G'':list A) a, nth_error (G'' ++ a :: G) (length G'') = Some a.
induction G''; intros; simpl; intuition eauto.
Save.

Lemma lookup_length2 : forall (A:Set) (G G'':list A) a n, nth_error (G'' ++ a :: G) (length G'' + S n) = nth_error G n.
induction G''; intros; simpl; auto.
Save.

Lemma lookup_length3 : forall (A:Set) (G:list A) n a, nth_error G n = Some a -> n < length G.
induction G; intros. destruct n; simpl; discriminate.
destruct n; simpl in *; auto with arith.
apply lt_n_S. eapply IHG; eauto.
Qed.

Lemma lookup_suffix : forall (A:Set) (G G' G'':list A) n a,
 length G' <= n ->
 nth_error (G' ++ G) n = Some a ->
 nth_error (G' ++ G'' ++ G) (length G'' + n) = Some a.
intros A G G' G'' n a. generalize G'. clear G'. induction n; intros; destruct G'.
 destruct G.
  discriminate.
  inversion H0. simpl. replace (length G''+0) with (length G'') by omega. apply lookup_length.
 simpl in H. inversion H.
 destruct G.
  discriminate.
  simpl in *. rewrite lookup_length2. assumption.
 replace (length G'' + S n) with (S (length G'' + n)) by omega. simpl in *. apply IHn.
  omega. assumption.
Save.

Lemma lookup_prefix : forall (A:Set) (G G'' G':list A) n a,
 n < length G' ->
 nth_error (G' ++ G) n = Some a ->
 nth_error (G' ++ G'' ++ G) n = Some a.
intros A G G'' G' n a. generalize G'. clear G'. induction n; intros; (destruct G'; [inversion H|]).
 trivial.
 simpl in *. apply IHn. omega. assumption.
Save.

Lemma add_not_empty : forall x s, ~VarSet.Empty (VarSet.add x s).
unfold VarSet.Empty. unfold not. intros. 
eapply H. apply VarSet.add_1. reflexivity.
Save.

Lemma add_equal : forall x s s', VarSetProps.Add x s s' -> VarSet.Equal s' (VarSet.add x s).
intros. unfold VarSetProps.Add in H. unfold VarSet.Equal. intro. split; intro.
 rewrite H in H0. intuition auto with set.
 rewrite H. destruct (eq_nat_dec x a); [left|right]; eauto with set.
Save.

Lemma shift2_step_twice : forall d c x U, VarSet.Equal (shift2_step d c x (shift2_step d c x U)) (shift2_step d c x U).
unfold shift2_step. intros.
destruct (le_lt_dec c x); apply VarSetProps.add_equal; apply VarSet.add_1; reflexivity.
Save.

Lemma shift2_step_transpose : forall d c x y U, VarSet.Equal (shift2_step d c x (shift2_step d c y U)) (shift2_step d c y (shift2_step d c x U)).
unfold shift2_step. intros.
destruct (le_lt_dec c x); destruct (le_lt_dec c y); rewrite VarSetProps.add_add; reflexivity.
Save.

(* FIXME: need to redo SetoidList.fold_right_add for when f is idemopotent, like shift2_step is *)

(*
Lemma fold_right_add_2 : forall d c i s' s x,
 NoDup s ->
 NoDup s' ->
 (forall y, InA (@eq nat) y s' <-> x = y \/ InA (@eq nat) y s) ->
 VarSet.Equal (fold_right (shift2_step d c) i s') (shift2_step d c x (fold_right (shift2_step d c) i s)).
induction s'.
 (* base case *)
 intros. assert (InA (@eq nat) x nil). rewrite H1. auto. inversion H2.
 (* step case *)
 simpl. intros.
 destruct (eq_nat_dec x a).
  subst. rewrite (IHs' s a).
   apply H.
   inversion H0. apply H5.
   intro. split; intro.
    rewrite <- H1. right. apply H2.
    destruct H2. subst. 
  
apply H1.  

 simpl. 

apply IH. reflexivity.



Lemma shift_varset_add : forall d c s x,
  VarSet.Equal (shift_varset d c (VarSet.add x s)) (shift2_step d c x (shift_varset d c s)).
intros.
elim s using VarSetProps.set_induction; intros.
 (* base *)
 rewrite (VarSetProps.empty_is_empty_1 H). rewrite shift_varset_empty.
 rewrite <- VarSetProps.singleton_equal_add. unfold shift2_step. destruct (le_lt_dec c x).
  rewrite shift_varset_singleton; auto using VarSetProps.singleton_equal_add.
  rewrite shift_varset_singleton2; auto using VarSetProps.singleton_equal_add.
 (* step *)
 assert (VarSet.Equal s' (VarSet.add x0 s0)). auto using add_equal.
 rewrite H2. destruct (eq_nat_dec x x0).
  subst. setoid_replace (VarSet.add x0 (VarSet.add x0 s0)) with (VarSet.add x0 s0).
   rewrite H. rewrite shift2_step_twice. reflexivity.
   apply VarSetProps.add_equal. apply VarSet.add_1. reflexivity.
 rewrite <- H2.
 destruct (VarSetProps.fold_0 (VarSet.add x s) VarSet.empty (shift2_step d c)) as [l [l_nodup [l_eq_xs l_fold_eq]]].
 destruct (VarSetProps.fold_0 s VarSet.empty (shift2_step d c)) as [l2 [l2_nodup [l2_eq_xs l2_fold_eq]]].
 rewrite l_fold_eq. rewrite l2_fold_eq. clear l_fold_eq l2_fold_eq.
 setoid_replace (shift2_step d c x (fold_right (shift2_step d c) VarSet.empty l2))
    with (fold_right (shift2_step d c) VarSet.empty (x::l2)).

generalize 




simpl. reflexivity.
*)

Lemma In_shift_varset : forall n n' s c d,
VarSet.In n s -> n'=(if le_lt_dec c n then d+n else n) -> VarSet.In n' (shift_varset d c s).
Proof.
 intros. subst n'. unfold shift_varset. apply VarSet.elements_1 in H. rewrite VarSet.fold_1. set (l:=VarSet.elements s) in *. generalize VarSet.empty. clearbody l. induction l.
  inversion H.
  inversion H; subst.
   unfold VarSet.E.eq in H1. subst a. intros. simpl. set (r:=shift2_step d c n t) in *.  assert (VarSet.In (if le_lt_dec c n then d + n else n) r).
    unfold r. unfold shift2_step. destruct (le_lt_dec c n); apply VarSet.add_1; reflexivity.
    clearbody r. generalize r H0. clear. induction l; intros.
     simpl. assumption.
     simpl. apply IHl. unfold shift2_step. destruct (le_lt_dec c a); apply VarSet.add_2; assumption.
   intros. simpl. apply IHl. assumption.
Qed.

Lemma shift_varset_In : forall n s c d,
 VarSet.In n (shift_varset d c s) -> VarSet.In (if le_lt_dec c n then n-d else n) s.
Proof.
 intros. unfold shift_varset in H. apply VarSet.elements_2. rewrite VarSet.fold_1 in H. set (l:=VarSet.elements s) in *. clearbody l. set (r:=VarSet.empty) in *. assert (~VarSet.In n r). apply VarSet.empty_1. clearbody r. generalize r H H0. clear. induction l; intros.
  simpl in H. contradiction.
  compare (if le_lt_dec c n then n - d else n) a; intros.
   subst a. left. reflexivity.
   right. eapply IHl. simpl in H. eassumption.
    unfold shift2_step. destruct (le_lt_dec c n); destruct (le_lt_dec c a);
    intro bad; destruct H0; (eapply VarSet.add_3; [|eassumption]); unfold VarSet.E.eq; omega.
Qed.

Lemma shift_varset_image : forall n s c d,
 VarSet.In n (shift_varset d c s) -> n < c \/ n >= c+d.
Proof.
 intros. unfold shift_varset in H. rewrite VarSet.fold_1 in H. set (l:=VarSet.elements s) in *. clearbody l. set (r:=VarSet.empty) in *. assert (forall n', VarSet.In n' r -> n'<c \/ n'>=c+d).
  intros. destruct (VarSet.empty_1 H0).
  clearbody r. generalize r H H0. clear. induction l; intros.
   simpl in H. auto.
   eapply IHl.
    simpl in H. apply H.
    unfold shift2_step. destruct (le_lt_dec c a); intros.
     compare n' (d+a); intros. omega.
     apply VarSet.add_3 in H1. auto. unfold VarSet.E.eq. auto.
     compare n' a; intros. omega.
     apply VarSet.add_3 in H1. auto. unfold VarSet.E.eq. auto.
Qed.

Lemma shift_varset_add : forall d c x s,
  ~VarSet.In x s ->
  VarSet.Equal (shift_varset d c (VarSet.add x s)) (shift2_step d c x (shift_varset d c s)).
intros. unfold shift_varset. apply VarSetProps.fold_add.
 apply varset_setoid.
 unfold compat_op. intros. unfold VarSet.E.eq in H0. subst x0. apply shift2_step_mor; auto.
 unfold transpose. intros. unfold shift2_step.
 destruct (le_lt_dec c x0); destruct (le_lt_dec c y); rewrite VarSetProps.add_add; reflexivity.
 assumption.
Save.

Lemma shift_down_add : forall x s,
 ~VarSet.In x s ->
 VarSet.Equal (shift_down (VarSet.add x s)) (shift_step x (shift_down s)).
intros. unfold shift_down. apply VarSetProps.fold_add.
 apply varset_setoid.
 unfold compat_op. unfold shift_step. intros. destruct x0; destruct x'.
  assumption.
  discriminate.
  discriminate. 
  inversion H0. rewrite H1. reflexivity.
 unfold transpose. intros. unfold shift_step.
 destruct x0; destruct y; try reflexivity; eauto using VarSetProps.add_add.
 assumption.
Save.

Lemma not_in_shift_varset_1 : forall U2 d c x, ~VarSet.In x U2 -> c<=x -> ~VarSet.In (d+x) (shift_varset d c U2).
intros U2. elim U2 using VarSetProps.set_induction; intros.
 rewrite (VarSetProps.empty_is_empty_1 H). rewrite shift_varset_empty. apply (VarSet.empty_1).
 assert (VarSet.Equal s' (VarSet.add x s)). auto using add_equal.
 rewrite H4 in H2.
 rewrite H4. rewrite shift_varset_add. 2:assumption.
 destruct (eq_nat_dec x x0).
  elimtype False. auto using VarSet.add_1.
  assert (~VarSet.In x0 s). auto using VarSet.add_2.
  unfold shift2_step. destruct (le_lt_dec c x); unfold not; intros.
   refine (H d _ _ H5 H3 (VarSet.add_3 (x:=d+x) _ H6)). unfold VarSet.E.eq. omega.
   refine (H d _ _ H5 H3 (VarSet.add_3 (x:=x) _ H6)). unfold VarSet.E.eq. omega.
Save.

Lemma not_in_shift_varset_2 : forall d c U2 x, ~VarSet.In x U2 -> x<c -> ~VarSet.In x (shift_varset d c U2).
intros d c U2. elim U2 using VarSetProps.set_induction; intros.
 rewrite (VarSetProps.empty_is_empty_1 H). rewrite shift_varset_empty. apply (VarSet.empty_1).
 assert (VarSet.Equal s' (VarSet.add x s)). auto using add_equal.
 rewrite H4 in H2.
 rewrite H4. rewrite shift_varset_add. 2:assumption.
 destruct (eq_nat_dec x x0).
  elimtype False. auto using VarSet.add_1.
  assert (~VarSet.In x0 s). auto using VarSet.add_2.
  unfold shift2_step. destruct (le_lt_dec c x); unfold not; intros.
   refine (H _ H5 H3 (VarSet.add_3 (x:=d+x) _ H6)). unfold VarSet.E.eq. omega.
   refine (H _ H5 H3 (VarSet.add_3 (x:=x) _ H6)). unfold VarSet.E.eq. omega.
Save.

Lemma shift_varset_empty_inter : forall d c U1 U2,
 VarSet.Empty (VarSet.inter U1 U2) ->
 VarSet.Empty (VarSet.inter (shift_varset d c U1) (shift_varset d c U2)).   
intros d c U1. elim U1 using VarSetProps.set_induction; intros.
 rewrite (VarSetProps.empty_is_empty_1 H). rewrite shift_varset_empty. auto with set.
 assert (VarSet.Equal s' (VarSet.add x s)). auto using add_equal.
 rewrite H3. rewrite shift_varset_add. 2:assumption.
 rewrite H3 in H2.
 assert (~VarSet.In x U2). destruct (VarSetProps.In_dec x U2).
  rewrite (VarSetProps.inter_add_1 s i) in H2. elimtype False. apply (add_not_empty _ _ H2).
  assumption.
 rewrite (VarSetProps.inter_add_2 s H4) in H2.
 unfold shift2_step. destruct (le_lt_dec c x).
  rewrite (VarSetProps.inter_add_2); auto using not_in_shift_varset_1.
  rewrite (VarSetProps.inter_add_2); auto using not_in_shift_varset_2.
Save.

Lemma shift2_step_union : forall d c U1 U2 x,
 VarSet.Equal (shift2_step d c x (VarSet.union U1 U2)) (VarSet.union (shift2_step d c x U1) U2).
intros. unfold shift2_step.
destruct (le_lt_dec c x); auto with set.
Save.

Lemma shift_varset_union : forall d c U1 U2, 
 VarSet.Equal (shift_varset d c (VarSet.union U1 U2)) (VarSet.union (shift_varset d c U1) (shift_varset d c U2)).
Proof.
intros. intro y. split; intro H.
 set (H1 := shift_varset_image _ _ _ _ H). clearbody H1. apply shift_varset_In in H.
 destruct (VarSet.union_1 H); [apply VarSet.union_2|apply VarSet.union_3]; (eapply In_shift_varset; [apply H0| destruct H1; destruct (le_lt_dec c y); destruct (le_lt_dec c (y-d)); destruct (le_lt_dec c y); omega]).

 destruct (VarSet.union_1 H); set (H1 := shift_varset_image _ _ _ _ H0); clearbody H1;
 apply shift_varset_In in H0 ; (apply In_shift_varset with (n:=(if le_lt_dec c y then y - d else y)); [| destruct H1; destruct (le_lt_dec c y); destruct (le_lt_dec c (y-d)); destruct (le_lt_dec c y); omega]).
  apply VarSet.union_2. assumption.
  apply VarSet.union_3. assumption.
Qed.

(*Lemma shift_varset_union : forall d c U1 U2, 
 VarSet.Equal (shift_varset d c (VarSet.union U1 U2)) (VarSet.union (shift_varset d c U1) (shift_varset d c U2)).
Admitted.
*)
Lemma shift_down_empty : VarSet.Equal (shift_down VarSet.empty) VarSet.empty.
unfold shift_down. rewrite VarSet.fold_1. rewrite elements_empty. reflexivity.
Save.

Lemma In_shift_down : forall n U,
  VarSet.In (S n) U -> VarSet.In n (shift_down U).
Proof.
  intros n U H. apply VarSet.elements_1 in H. unfold shift_down. rewrite VarSet.fold_1. set (l:=VarSet.elements U) in *. clearbody l. clear U. generalize VarSet.empty. induction l.
   inversion H.
   intro s0. simpl. inversion H; subst.
    change VarSet.E.eq with (eq (A:=nat)) in H1. subst a. simpl.   set (s1:=VarSet.add n s0). assert (VarSet.In n s1) by (unfold s1; apply VarSet.add_1; reflexivity). generalize s1 H0. clear . induction l; intros.
     simpl. assumption.
     simpl. assert (VarSet.In n (shift_step a s1)) by (unfold shift_step; destruct a; auto using VarSet.add_2). apply IHl. assumption.
    apply IHl. assumption.
Qed.

Lemma shift_down_In : forall n U,
  VarSet.In n (shift_down U) -> VarSet.In (S n) U.
Proof.
  intros n U H. apply VarSet.elements_2. unfold shift_down in H. rewrite VarSet.fold_1 in H. set (l:=VarSet.elements U) in *. clearbody l. assert (~VarSet.In n VarSet.empty). apply VarSet.empty_1. generalize H H0. generalize VarSet.empty. clear. induction l; intros.
   simpl in H. contradiction.
   simpl in H. compare a (S n); intro an.
    subst a. left. reflexivity.
    right. eapply IHl. apply H. unfold shift_step. destruct a. assumption.
     assert (~VarSet.E.eq a n). change VarSet.E.eq with (eq (A:=nat)). intro an'. subst a. destruct an. reflexivity.
     intro inadded. destruct H0. eapply VarSet.add_3; eauto.
Qed.

Lemma down_shift : forall d c U x, VarSet.Equal (shift_down (shift2_step d (S c) (S x) U)) (shift2_step d c x (shift_down U)).
intros. unfold shift2_step. destruct (le_lt_dec (S c) (S x)); destruct (le_lt_dec c x); try (elimtype False; clear - l l0; omega).
 rewrite <- plus_Snm_nSm.
 destruct (VarSetProps.In_dec (S d + x) U).
  rewrite VarSetProps.add_equal; auto. rewrite VarSetProps.add_equal; [reflexivity|apply In_shift_down;assumption].
  rewrite shift_down_add; auto. simpl. reflexivity.
 destruct (VarSetProps.In_dec (S x) U).
  rewrite VarSetProps.add_equal; auto. rewrite VarSetProps.add_equal; [reflexivity|apply In_shift_down;assumption].
  rewrite shift_down_add; auto. simpl. reflexivity.
Qed.

Lemma shift_down_varset : forall d c U, VarSet.Equal (shift_down (shift_varset d (S c) U)) (shift_varset d c (shift_down U)).
intros d c U. elim U using VarSetProps.set_induction; intros.
 (* base *)
 rewrite (VarSetProps.empty_is_empty_1 H).
 rewrite shift_down_empty. rewrite shift_varset_empty.  
 rewrite shift_down_empty. rewrite shift_varset_empty. reflexivity.
 (* step *)
 assert (VarSet.Equal s' (VarSet.add x s)). auto using add_equal.
 rewrite H2.
 rewrite shift_varset_add. 2:assumption.
 rewrite shift_down_add. 2:assumption.
 case_eq x; intros.
  subst x. unfold shift2_step. simpl. rewrite shift_down_add. 2:(apply not_in_shift_varset_2; auto with arith). simpl. assumption.
  simpl. rewrite shift_varset_add.
   rewrite down_shift. rewrite H. reflexivity.
   intro H'. destruct H0. rewrite H3. apply shift_down_In. assumption.
Qed.
(*
Lemma shift_down_varset_2 : forall s,
 VarSet.Equal s (shift_down (shift_varset 1 1 s)).
Proof.
 intros. elim s using VarSetProps.set_induction; intros.
  rewrite (VarSetProps.empty_is_empty_1 H). rewrite shift_varset_empty. rewrite shift_down_empty. reflexivity.
  assert (VarSet.Equal s' (VarSet.add x s0)). auto using add_equal.
  rewrite H2.
  rewrite shift_varset_add. assumption.
  unfold shift2_step.
  rewrite shift_down_add. assumption.
  *)
  

Lemma shift_preserves_typing : forall Gi G G' G'' t A U,
 prf Gi (G'++G) t A U ->
 prf Gi (G'++G''++G) (l_shift (length G'') (length G') t) A (shift_varset (length G'') (length G') U).
intros Gi G G' G'' t A U prf_t.
set (Gx:=G'++G) in *. set (Gx_eq:=refl_equal Gx:Gx=G'++G).
generalize G' Gx_eq. clear Gx_eq.
induction prf_t; intros; simpl; subst G0.
 (* ivar *)
 rewrite H0. econstructor. assumption. apply shift_varset_empty.
 (* lvar *)
 rewrite H0.
 destruct (le_lt_dec (length G'0) n) as [lenG_le_n | n_lt_lenG].
  econstructor; eauto using lookup_suffix, shift_varset_singleton.
  constructor; eauto using lookup_prefix, shift_varset_singleton2.
 (* i_intro *)
 rewrite H. constructor; eauto using shift_varset_empty.
 (* tensor_intro *)
 rewrite H0. econstructor; eauto using shift_varset_empty_inter, shift_varset_union.
 (* tensor_elim *)
 rewrite H0. econstructor.
  apply IHprf_t1. reflexivity.
  replace (A::B::G'0++G''++G) with ((A::B::G'0)++G''++G).
   change (S (S (length G'0))) with (length (A::B::G'0)). apply IHprf_t2.
    rewrite app_comm_cons. rewrite app_comm_cons. reflexivity.
   rewrite app_comm_cons. rewrite app_comm_cons. reflexivity.
  simpl. rewrite shift_down_varset. rewrite shift_down_varset. apply shift_varset_empty_inter. assumption.
  simpl. rewrite shift_down_varset. rewrite shift_down_varset. apply shift_varset_union; assumption.
 (* t_and_intro *)
 rewrite H. econstructor.
  apply IHprf_t1. reflexivity.
  apply IHprf_t2. reflexivity.
  apply shift_varset_union.
 (* t_and_elim1 *)
 econstructor; auto.
 (* t_and_elim2 *)
 econstructor; auto.
 (* t_lolli_intro *)
 rewrite H. econstructor.
  replace (A::G'0++G''++G) with ((A::G'0)++G''++G).
   change (S (length G'0)) with (length (A::G'0)). apply IHprf_t.
    rewrite app_comm_cons. reflexivity.
   rewrite app_comm_cons. reflexivity.
  simpl. rewrite shift_down_varset. reflexivity.
 (* t_lolli_elim *)
 rewrite H0. econstructor; eauto using shift_varset_empty_inter, shift_varset_union.
 (* t_bang_intro *)
 econstructor; auto.
  rewrite (VarSetProps.empty_is_empty_1 H). rewrite shift_varset_empty. apply VarSet.empty_1.
 (* t_bang_elim *)
 rewrite H0. econstructor; auto using shift_varset_empty_inter, shift_varset_union.
 (* t_axiom *)
 econstructor. auto.
 (* t_let *)
 rewrite H1. rewrite H in *. econstructor.
  apply IHprf_t1. reflexivity.
  replace (A::G'0++G''++G) with ((A::G'0)++G''++G).
   change (S (length G'0)) with (length (A::G'0)). apply IHprf_t2. reflexivity.
   reflexivity.
   reflexivity.
  change (length (A::G'0)) with (S (length G'0)). rewrite shift_down_varset. apply shift_varset_empty_inter. assumption.
  change (length (A::G'0)) with (S (length G'0)). rewrite shift_varset_union. rewrite shift_down_varset. reflexivity.
Save.

(*
Lemma subst_preserve_typing :
 prf Gi G t A U1 ->
 prf Gi (G'++A::G) t' B U2 ->
 prf Gi (
*)

Lemma prf_uses_ctx : forall Gi G t A U,
 prf Gi G t A U -> forall n, VarSet.In n U -> n < length G.
Proof.
 induction 1; intros; auto.
  rewrite H0 in H1. destruct (VarSet.empty_1 H1).
  rewrite H0 in H1. apply VarSet.singleton_1 in H1. unfold VarSet.E.eq in H1. subst n0. generalize G H. clear G H H0. induction n; intros.
   simpl in H. destruct G. discriminate. simpl. auto with arith.
   destruct G. discriminate. simpl in *. apply lt_n_S. auto.
  rewrite H in H0. destruct (VarSet.empty_1 H0).
  rewrite H2 in H3. destruct (VarSet.union_1 H3); auto.
  rewrite H2 in H3. destruct (VarSet.union_1 H3); auto. repeat apply shift_down_In in H4. apply IHprf2 in H4. simpl in H4.  auto using lt_S_n.
  rewrite H1 in H2. destruct (VarSet.union_1 H2); auto.
  rewrite H0 in H1. apply shift_down_In in H1. apply IHprf in H1. simpl in H1. auto using lt_S_n.
  rewrite H2 in H3. destruct (VarSet.union_1 H3); auto.
  rewrite H2 in H3. destruct (VarSet.union_1 H3); auto.
  rewrite H3 in H4. rewrite H1 in H4. destruct (VarSet.union_1 H4). auto. apply shift_down_In in H5. apply IHprf2 in H5. auto using lt_S_n.
Qed.

Lemma proof_weakening : forall Gi G G' t A U,
 prf Gi G t A U -> prf Gi (G++G') t A U.
Proof.
 intros.
 replace (G++G') with (G++G'++nil).
 replace t with (l_shift (length G') (length G) t).
 setoid_replace U with (shift_varset (length G') (length G) U).
 apply shift_preserves_typing.
 rewrite <- List.app_nil_end. assumption.
 intros x.
 split.
  intros xinu.
  apply prf_uses_ctx with (n:=x) in H. 2:assumption.
  eapply In_shift_varset.
  apply xinu.
  destruct (le_lt_dec (length G)); omega.

  intro xinsu.
  destruct (shift_varset_image _ _ _ _ xinsu).
  apply shift_varset_In in xinsu.
  destruct (le_lt_dec (length G)). elimtype False. omega.
  assumption.
  apply shift_varset_In in xinsu.
  apply prf_uses_ctx with (n:=(if le_lt_dec (length G) x then x - length G' else x)) in H. 2:assumption.
  destruct (le_lt_dec (length G)). elimtype False. omega.
  assumption.

  induction H; simpl in *; auto; try (rewrite IHprf1; rewrite IHprf2; auto); try (rewrite IHprf; auto).
    apply lookup_length3 in H. destruct (le_lt_dec (length G) n). elimtype False. omega. reflexivity.

  rewrite <- app_nil_end.  reflexivity.
Qed.


Definition sumbool_to_bool : forall (A B:Prop), {A}+{B} -> bool :=
  fun A B x => if x then true else false.
Implicit Arguments sumbool_to_bool [A B].

Fixpoint proof_checker (Gi:context)
                       (G:context)
                       (t:prf_term)
                       {struct t}
                     : option (formula * VarSet.t)
 :=
 match t with
 | t_lvar n =>
    A <- nth_error G n;:
    ret (A, VarSet.singleton n)
 | t_ivar n =>
    A <- nth_error Gi n;:
    ret (A, VarSet.empty)
 | t_i_intro =>
    ret (f_i, VarSet.empty)
 | t_tensor_intro t1 t2 =>
    x1 <- proof_checker Gi G t1;:
    x2 <- proof_checker Gi G t2;:
    let (A, U1) := x1 in
    let (B, U2) := x2 in
    lift_bool (VarSet.is_empty (VarSet.inter U1 U2));;
    ret (f_tensor A B, VarSet.union U1 U2)
 | t_tensor_elim t1 t2 =>
    x1 <- proof_checker Gi G t1;:
    match x1 with
    | (f_tensor A B, U1) =>
        x2 <- proof_checker Gi (A::B::G) t2;:
        let (C, U2) := x2 in
        let U2' := shift_down (shift_down U2) in
        lift_bool (VarSet.is_empty (VarSet.inter U1 U2'));;
        ret (C, VarSet.union U1 U2')
    | _ =>
        fail
    end
 | t_and_intro t1 t2 =>
    x1 <- proof_checker Gi G t1;:
    x2 <- proof_checker Gi G t2;:
    let (A, U1) := x1 in
    let (B, U2) := x2 in
    ret (f_and A B, VarSet.union U1 U2)
 | t_and_elim1 t =>
    x <- proof_checker Gi G t;:
    match x with
    | (f_and A B, U) =>
        ret (A, U)
    | _ => fail
    end
 | t_and_elim2 t =>
    x <- proof_checker Gi G t;:
    match x with
    | (f_and A B, U) =>
        ret (B, U)
    | _ => fail
    end
 | t_lolli_intro A t =>
    x <- proof_checker Gi (A::G) t;:
    let (B,U) := x in
    ret (f_lolli A B, shift_down U)
 | t_lolli_elim t1 t2 =>
    x1 <- proof_checker Gi G t1;:
    match x1 with
    | (f_lolli A B, U1) =>
        x2 <- proof_checker Gi G t2;:
        let (A', U2) := x2 in
        lift_bool (sumbool_to_bool (formula_eq_dec A A'));;
        lift_bool (VarSet.is_empty (VarSet.inter U1 U2));;
        ret (B, VarSet.union U1 U2)
    | _ =>
        fail
    end
 | t_bang_intro t =>
    x <- proof_checker Gi G t;:
    let (A,U) := x in
    lift_bool (VarSet.is_empty U);;
    ret (f_bang A, U)
 | t_bang_elim t1 t2 =>
    x1 <- proof_checker Gi G t1;:
    match x1 with
    | (f_bang A, U1) =>
        x2 <- proof_checker (A::Gi) G t2;:
        let (C, U2) := x2 in
        lift_bool (VarSet.is_empty (VarSet.inter U1 U2));;
        ret (C, VarSet.union U1 U2)
    | _ =>
        fail
    end
 | t_axiom ax t =>
    x <- proof_checker Gi G t;:
    let (A,U) := x in
    lift_bool (sumbool_to_bool (formula_eq_dec A (axiom_domain ax)));;
    ret (axiom_codomain ax, U)
 | t_let t1 t2 =>
   x1 <- proof_checker Gi G t1;:
   let (A, U1) := x1 in
   x2 <- proof_checker Gi (A::G) t2;:
   let (B, Ut2) := x2 in
   let U2 := shift_down Ut2 in
   lift_bool (VarSet.is_empty (VarSet.inter U1 U2));;
   ret (B, VarSet.union U1 U2)
 end.

Hint Resolve VarSet.is_empty_2.

Lemma proof_checker_sound : forall Gi G t A U,
  proof_checker Gi G t = Some (A, U) ->
  prf Gi G t A U.
intros Gi G t A U. generalize Gi G A U. clear Gi G A U.
induction t; intros.
 (* t_lvar *)
 simpl in H.
 destruct (option_dec (nth_error G n)) as [[A' A'_res] | A'_res]; rewrite A'_res in H; try discriminate.
 inversion H. subst. apply prf_lvar. assumption. reflexivity.
 (* t_ivar *)
 simpl in H.
 destruct (option_dec (nth_error Gi n)) as [[A' A'_res] | A'_res]; rewrite A'_res in H; try discriminate.
 inversion H. subst. apply prf_ivar. assumption. reflexivity.
 (* t_i_intro *)
 inversion H. subst. apply prf_i_intro. reflexivity.
 (* t_tensor_intro *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t1)) as [[[A' U1] t1_check] | t1_check]; rewrite t1_check in H; try discriminate.
 destruct (option_dec (proof_checker Gi G t2)) as [[[B U2] t2_check] | t2_check]; rewrite t2_check in H; try discriminate.
 simpl in H.
 destruct (bool_dec (VarSet.is_empty (VarSet.inter U1 U2))) as [inter_check | inter_check]; rewrite inter_check in H; try discriminate.
 inversion H. subst. econstructor; intuition eauto. reflexivity.
 (* t_tensor_elim *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t1)) as [[[A' U1] t1_check] | t1_check]; rewrite t1_check in H; try discriminate.
 simpl in H.
 destruct A'; try discriminate.
 destruct (option_dec (proof_checker Gi (A'1::A'2::G) t2)) as [[[B U2] t2_check] | t2_check]; rewrite t2_check in H; try discriminate.
 simpl in H.
 destruct (bool_dec (VarSet.is_empty (VarSet.inter U1 (shift_down (shift_down U2))))) as [inter_check | inter_check]; rewrite inter_check in H; try discriminate.
 inversion H. subst. econstructor; intuition eauto. reflexivity.
 (* t_and_intro *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t1)) as [[[A' U1] t1_check] | t1_check]; rewrite t1_check in H; try discriminate.
 destruct (option_dec (proof_checker Gi G t2)) as [[[B U2] t2_check] | t2_check]; rewrite t2_check in H; try discriminate.
 inversion H. subst. econstructor; intuition eauto. reflexivity.
 (* t_and_elim1 *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t)) as [[[A' U1] t_check] | t_check]; rewrite t_check in H; try discriminate.
 simpl in H. destruct A'; try discriminate.
 inversion H. subst. econstructor; eauto.
 (* t_and_elim2 *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t)) as [[[A' U1] t_check] | t_check]; rewrite t_check in H; try discriminate.
 simpl in H. destruct A'; try discriminate.
 inversion H. subst. econstructor; eauto.
 (* t_lolli_intro *)
 simpl in H.
 destruct (option_dec (proof_checker Gi (f::G) t)) as [[[B U1] t_check] | t_check]; rewrite t_check in H; try discriminate.
 inversion H. subst. econstructor; eauto. reflexivity.
 (* t_lolli_elim *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t1)) as [[[A' U1] t1_check] | t1_check]; rewrite t1_check in H; try discriminate.
 simpl in H. destruct A'; try discriminate.
 destruct (option_dec (proof_checker Gi G t2)) as [[[A' U2] t2_check] | t2_check]; rewrite t2_check in H; try discriminate.
 simpl in H.
 destruct (formula_eq_dec A'1 A') as [fs_eq | fs_neq]; try discriminate. simpl in H.
 destruct (bool_dec (VarSet.is_empty (VarSet.inter U1 U2))) as [inter_check | inter_check]; rewrite inter_check in H; try discriminate.
 inversion H. subst. econstructor; eauto. reflexivity.
 (* t_bang_intro *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t)) as [[[A' U1] t_check] | t_check]; rewrite t_check in H; try discriminate.
 simpl in H.
 destruct (bool_dec (VarSet.is_empty U1)) as [empty_check | empty_check]; rewrite empty_check in H; try discriminate.
 inversion H. subst. econstructor; eauto.
 (* t_bang_elim *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t1)) as [[[A' U1] t1_check] | t1_check]; rewrite t1_check in H; try discriminate.
 simpl in H; destruct A'; try discriminate.
 destruct (option_dec (proof_checker (A'::Gi) G t2)) as [[[B U2] t2_check] | t2_check]; rewrite t2_check in H; try discriminate.
 simpl in H.
 destruct (bool_dec (VarSet.is_empty (VarSet.inter U1 U2))) as [inter_check | inter_check]; rewrite inter_check in H; try discriminate.
 inversion H. subst. econstructor; eauto. reflexivity.
 (* t_axiom *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t)) as [[[A' U1] t_check] | t_check]; rewrite t_check in H; try discriminate.
 simpl in H.
 destruct (formula_eq_dec A' (axiom_domain a)) as [is_equal | not_equal]; try discriminate.
 inversion H. clear H. subst. econstructor; eauto.
 (* t_let *)
 simpl in H.
 destruct (option_dec (proof_checker Gi G t1)) as [[[A' U1] t1_check] | t1_check]; rewrite t1_check in H; try discriminate.
 simpl in H.
 destruct (option_dec (proof_checker Gi (A'::G) t2)) as [[[B Ut2] t2_check] | t2_check]; rewrite t2_check in H; try discriminate.
 simpl in H.
 destruct (bool_dec (VarSet.is_empty (VarSet.inter U1 (shift_down Ut2)))) as [inter_check | inter_check]; rewrite inter_check in H; try discriminate.
 inversion H. subst. econstructor; eauto. reflexivity. reflexivity.
Save.

Definition proof_check (Gi G:context) (t:prf_term)
  : { B : formula | exists U, prf Gi G t B U }+{True}
  := match proof_checker Gi G t as l return proof_checker Gi G t = l -> { B : formula | exists U, prf Gi G t B U }+{True} with
     | None        => fun e : _ =>
        inright _ I
     | Some (B, U) => fun e : proof_checker Gi G t = Some (B, U) =>
(* coq suddenly seems to require more details, not sure why...
        inleft _ (exist _ B (ex_intro _ U (proof_checker_sound Gi G t B U e)))
 *)
        inleft True (exist (fun B => exists U, prf Gi G t B U) B (ex_intro (fun U => prf Gi G t B U) U (proof_checker_sound Gi G t B U e)))
     end (refl_equal (proof_checker Gi G t)).

Definition implies : formula -> formula -> Prop :=
  fun A B => exists t, exists U, prf nil (A::nil) t B U.

Lemma implies_refl : forall A, implies A A.
intro A.
exists (t_lvar 0).
exists (VarSet.singleton 0%nat).
apply proof_checker_sound. reflexivity.
Save.

Lemma implies_trans : forall A B C, implies A B -> implies B C -> implies A C.

intros A B C [tAB [UAB pAB]] [tBC [UBC pBC]].
exists (t_lolli_elim (t_lolli_intro B (l_shift (length (A::nil)) (length (B::nil)) tBC)) tAB).
eapply ex_intro.
(*assert (prf nil (B::A::nil) (t_lolli_intro B (l_shift (length (A::nil)) (length (B::nil)) tBC)) (f_lolli B C) *)
eapply prf_lolli_elim.
  eapply prf_lolli_intro.
    change (B::A::nil) with ((B::nil)++(A::nil)++nil).
    apply shift_preserves_typing.
    eassumption.

    reflexivity.

    eassumption.

    intros x inboth.
    pose (inbc := VarSet.inter_1 inboth).
    pose (inab := VarSet.inter_2 inboth).
    apply prf_uses_ctx with (n:=x) in pAB; auto.
    apply shift_down_In in inbc. pose (shift := shift_varset_image _ _ _ _ inbc). clearbody shift. apply shift_varset_In in inbc. simpl in inbc. rewrite <- minus_n_O in inbc.
    apply prf_uses_ctx with (n:=x) in pBC; auto.
    simpl in *. omega.

    reflexivity.
Qed.

Lemma lookup_neq : forall (A:Set) (G G'':list A) a b n, n<>(length G'') -> nth_error (G'' ++ a :: G) n = nth_error (G'' ++ b :: G) n.
induction G''; intros; simpl in *.
destruct n. destruct H; reflexivity. simpl. reflexivity.
destruct n; simpl. reflexivity. auto.
Save.

Set Implicit Arguments.
Lemma subst_and_1 : forall Gi G G' A C t B U,
  prf Gi (G++A::G') t B U ->
  exists t', prf Gi (G++(f_and A C)::G') t' B U.
Proof.
  intros. set (G0:=(G++A::G')) in *. assert (G0 = (G++A::G')) by reflexivity. generalize G H0. clear H0. induction H; intros.
  eapply ex_intro; eauto using prf_ivar.
   compare n (length G1); intro; eapply ex_intro.
    eapply prf_and_elim1. rewrite e in H. rewrite H1 in H. rewrite lookup_length in H. injection H as H'. subst A0. apply prf_lvar.
     apply lookup_length.
     rewrite <- e. assumption.
    apply prf_lvar. rewrite <- H. rewrite H1. apply lookup_neq. assumption. assumption.
  eapply ex_intro. eauto using prf_i_intro.
  destruct (IHprf1 G1 H3); destruct (IHprf2 G1 H3); eapply ex_intro; eapply prf_tensor_intro; eauto.
  destruct (IHprf1 G1 H3); destruct (IHprf2 (A0::B::G1)). rewrite H3. simpl. reflexivity. eauto using prf_tensor_elim.
  destruct (IHprf1 G1 H2); destruct (IHprf2 G1 H2); eapply ex_intro; eapply prf_and_intro; eauto.
  destruct (IHprf G1 H0); eauto using prf_and_elim1.
  destruct (IHprf G1 H0); eauto using prf_and_elim2.
  destruct (IHprf (A0::G1)). rewrite H1. simpl. reflexivity. eauto using prf_lolli_intro.
  destruct (IHprf1 G1 H3); destruct (IHprf2 G1 H3); eapply ex_intro; eauto using prf_lolli_elim.
  destruct (IHprf G1 H1); eauto using prf_bang_intro.
  destruct (IHprf1 G1 H3); destruct (IHprf2 G1 H3); eapply ex_intro; eauto using prf_bang_elim.
  destruct (IHprf G1 H0); eauto using prf_axiom.
  destruct (IHprf1 G1 H4); destruct (IHprf2 (A0::G1)). rewrite H4. simpl. reflexivity. eauto using prf_let.
Qed.
Lemma subst_and_2 : forall Gi G G' A C t B U,
  prf Gi (G++A::G') t B U ->
  exists t', prf Gi (G++(f_and C A)::G') t' B U.
Proof.
  intros. set (G0:=(G++A::G')) in *. assert (G0 = (G++A::G')) by reflexivity. generalize G H0. clear H0. induction H; intros.
  eapply ex_intro; eauto using prf_ivar.
   compare n (length G1); intro; eapply ex_intro.
    eapply prf_and_elim2. rewrite e in H. rewrite H1 in H. rewrite lookup_length in H. injection H as H'. subst A0. apply prf_lvar.
     apply lookup_length.
     rewrite <- e. assumption.
    apply prf_lvar. rewrite <- H. rewrite H1. apply lookup_neq. assumption. assumption.
  eapply ex_intro. eauto using prf_i_intro.
  destruct (IHprf1 G1 H3); destruct (IHprf2 G1 H3); eapply ex_intro; eapply prf_tensor_intro; eauto.
  destruct (IHprf1 G1 H3); destruct (IHprf2 (A0::B::G1)). rewrite H3. simpl. reflexivity. eauto using prf_tensor_elim.
  destruct (IHprf1 G1 H2); destruct (IHprf2 G1 H2); eapply ex_intro; eapply prf_and_intro; eauto.
  destruct (IHprf G1 H0); eauto using prf_and_elim1.
  destruct (IHprf G1 H0); eauto using prf_and_elim2.
  destruct (IHprf (A0::G1)). rewrite H1. simpl. reflexivity. eauto using prf_lolli_intro.
  destruct (IHprf1 G1 H3); destruct (IHprf2 G1 H3); eapply ex_intro; eauto using prf_lolli_elim.
  destruct (IHprf G1 H1); eauto using prf_bang_intro.
  destruct (IHprf1 G1 H3); destruct (IHprf2 G1 H3); eapply ex_intro; eauto using prf_bang_elim.
  destruct (IHprf G1 H0); eauto using prf_axiom.
  destruct (IHprf1 G1 H4); destruct (IHprf2 (A0::G1)). rewrite H4. simpl. reflexivity. eauto using prf_let.
Qed.
Unset Implicit Arguments.

Lemma implies_subformulae : forall f1 f2 f1' f2' fo,
  implies f1 f1' -> implies f2 f2' -> fo = f_tensor \/ fo = f_and ->
  implies (fo f1 f2) (fo f1' f2').
Proof.
 intros until fo. intros [t1 [U1 p1]] [t2 [U2 p2]] [fo_eq|fo_eq]; subst fo.
 unfold implies. do 2 eapply ex_intro.
 eapply prf_tensor_elim.
  apply prf_lvar with (n:=0).
   simpl. reflexivity.
   reflexivity.
  eapply prf_tensor_intro.
   change (f1 :: f2 :: f_tensor f1 f2 :: nil) with ((f1::nil)++(f2::f_tensor f1 f2::nil)++nil). apply shift_preserves_typing. apply p1.
   change (f1 :: f2 :: f_tensor f1 f2 :: nil) with (nil++(f1::nil)++(f2::f_tensor f1 f2::nil)). apply shift_preserves_typing. change (nil ++ f2 :: f_tensor f1 f2 :: nil) with ((f2::nil)++(f_tensor f1 f2::nil)++nil). apply shift_preserves_typing. apply p2.
   simpl. intros x in_inter.
   pose (inu1 := VarSet.inter_1 in_inter). pose (inu2 := VarSet.inter_2 in_inter).
   pose (x1 := shift_varset_image _ _ _ _ inu1). clearbody x1. pose (x2 := shift_varset_image _ _ _ _ inu2). clearbody x2. apply shift_varset_In in inu2. pose (x2' := shift_varset_image _ _ _ _ inu2). clearbody x2'. apply shift_varset_In in inu2.
   match type of inu2 with VarSet.In ?x2 U2 => set (n2:=x2) end. apply prf_uses_ctx with (n:=n2) in p2; auto.
   destruct (le_lt_dec 0 x); destruct (le_lt_dec 1 (x-1)); unfold n2 in *; simpl in *; omega.
  reflexivity.
  simpl. intros x in_inter.
  pose (inu1 := VarSet.inter_1 in_inter). pose (inu2 := VarSet.inter_2 in_inter).
  rewrite <- (VarSet.singleton_1 inu1) in *. do 2 apply shift_down_In in inu2.
  destruct (VarSet.union_1 inu2). apply shift_varset_image in H. omega.
  apply shift_varset_In in H. simpl in H. apply shift_varset_image in H. omega.
  reflexivity.

 unfold implies.
 change (f1::nil) with (nil++(f1::nil)++nil) in p1. destruct (subst_and_1 _ _ _ f2 p1). simpl in H.
 change (f2::nil) with (nil++(f2::nil)++nil) in p2. destruct (subst_and_2 _ _ _ f1 p2). simpl in H0.
 do 2 eapply ex_intro. eapply prf_and_intro.
  apply H.
  apply H0.
  reflexivity.
Qed.
(*
Lemma implies_lolli : forall f1 f2 f1' f2',
  implies f1 f1' -> implies f2 f2' ->
  implies (f_lolli f1' f2) (f_lolli f1 f2').
Proof.
 intros f1 f2 f1' f2' [t1 [U1 p1]] [t2 [U2 p2]].
 unfold implies. do 2 eapply ex_intro. eapply prf_lolli_intro.
  eapply prf_lolli_elim.
*)
Definition proof_check_single (A B:formula) (t:prf_term)
  : { implies A B }+{True}
  := match proof_check nil (A::nil) t with
     | inleft (exist B' H) =>
        match formula_eq_dec B' B with
        | left B'_eq_B =>
           left _ (ex_intro _ t (eq_ind _ _ H _ B'_eq_B))
        | right _ =>
           right _ I
        end
     | inright _ => right _ I
     end.

Definition r_may := fun c f =>
  match R_new c with
    | None => f_i
    | Some r => f r
  end.

Definition resexpr_to_formula : res_expr B.Classname.t -> formula := 
let r_to_f_step (f:formula) (r:res_expr B.Classname.t) :=
  List.fold_left (fun f expr =>
    f_tensor f (match expr with (true,c) => r_may c (fun r => f_bang (f_atom r)) | (false,c) => r_may c (fun r => f_atom r) end))
    r f
in r_to_f_step f_i.

End MkILLSyntax.

Module MkILLSemantics
  (B   : BASICS)
  (BASESEM : ILL_BASE_SEMANTICS B)
  (SYN : ILL_SYNTAX B BASESEM.SYN)
  : ILL_SEMANTICS B BASESEM SYN.

Import SYN.
Import BASESEM.SYN.

(*Lemma VarSet_Equal_refl : forall s, VarSet.Equal s s.
unfold VarSet.Equal. tauto.
Save.

Lemma VarSet_Equal_symm : forall s1 s2, VarSet.Equal s1 s2 -> VarSet.Equal s2 s1.
unfold VarSet.Equal. firstorder.
Save.

Lemma VarSet_Equal_trans : forall s1 s2 s3, VarSet.Equal s1 s2 -> VarSet.Equal s2 s3 -> VarSet.Equal s1 s3.
unfold VarSet.Equal. firstorder.
Save.

Add Relation VarSet.t VarSet.Equal
 reflexivity proved by VarSet_Equal_refl
 symmetry proved by VarSet_Equal_symm
 transitivity proved by VarSet_Equal_trans
 as VarSet_Equal.

Add Morphism VarSet.Empty with signature VarSet.Equal ==> iff as VarSet_Empty_mor.
unfold VarSet.Equal. unfold VarSet.Empty. firstorder.
Save.

Add Morphism VarSet.In with signature eq ==> VarSet.Equal ==> iff as VarSet_In_mor.
unfold VarSet.Equal. firstorder.
Save.*)

Fixpoint context_to_formula (G:context) (n:nat) (U:VarSet.t)
                            {struct G}
                          : formula :=
  match G with
  | nil => f_i
  | cons f rest => if VarSet.mem n U then f_tensor f (context_to_formula rest (S n) U)
                                     else context_to_formula rest (S n) U
  end.

Add Morphism context_to_formula with signature (@eq context) ==> (@eq nat) ==> VarSet.Equal ==> (@eq formula) as ctf_mor.
induction y; intros x0 x1 x2 H.
 reflexivity.
 simpl. unfold VarSet.Equal in H. destruct (bool_dec (VarSet.mem x0 x1)).
  rewrite H0. rewrite (@VarSet.mem_1 x2 x0).
   rewrite (IHy (S x0) x1 x2 H); reflexivity.
   rewrite <- H. apply VarSet.mem_2. assumption.
  rewrite H0. replace (VarSet.mem x0 x2) with false. eauto.
   destruct (bool_dec (VarSet.mem x0 x2)).
    rewrite (@VarSet.mem_1 x1 x0) in H0. discriminate. rewrite H. apply VarSet.mem_2. assumption.
    congruence.
Save.

Import BASESEM.
Import RA.

Fixpoint icontext_to_formula (G:context) : formula :=
  match G with
  | nil => f_i
  | cons f rest => f_tensor f (icontext_to_formula rest)
  end.

Lemma right_weaken : forall r1 r2 r,
  r1 :*: r2 <: r ->
  r1 <: r.
intros.
rewrite <- (r_combine_e r1).
eapply leq_trans.
 apply combine_order. apply leq_refl. apply eq_refl. apply (e_bottom r2).
 assumption.
Save.

Lemma left_weaken : forall r1 r2 r,
  r1 :*: r2 <: r ->
  r2 <: r.
intros.
rewrite <- (e_combine_r r2).
eapply leq_trans.
 apply combine_order. apply e_bottom. apply leq_refl. reflexivity.
 apply H.
Save.

(*
FIXME: this doesn't work because setoid doesn't know that ILL.RA.res is a setoid
but it turns out we didn't need it anyway

Add Morphism sat : sat_morphism.
intros r1 r2 r1_eq_r2 A.
generalize r1 r2 r1_eq_r2. clear r1 r2 r1_eq_r2.
induction A; intros.
 (* f_i *)
 intuition.
 (* f_atom *)
 simpl. rewrite r1_eq_r2. intuition.
 (* f_tensor *)
 simpl. split; intros.
  destruct H as [r3 [r4 [r3r4_r1 [sat_r3 sat_r4]]]].
  exists r3. exists r4. rewrite <- r1_eq_r2. intuition.
  destruct H as [r3 [r4 [r3r4_r1 [sat_r3 sat_r4]]]].
  exists r3. exists r4. rewrite r1_eq_r2. intuition.
 (* f_and *)
 simpl. rewrite (IHA1 r1 r2 r1_eq_r2). rewrite (IHA2 r1 r2 r1_eq_r2). intuition.
 (* f_lolli *)
 simpl. split; intros.
  rewrite (IHA2 (r2 :*: r') (r1 :*: r')).
   rewrite <- r1_eq_r2. reflexivity.
   auto.
  rewrite (IHA2 (r1 :*: r') (r2 :*: r')).
   rewrite <- r1_eq_r2. reflexivity.
   auto.
 (* f_bang *)
 simpl. split; intros.
  destruct H as [r3 [r3_r2 sat_r2]].
  exists r3. rewrite <- r1_eq_r2. intuition.
  destruct H as [r3 [r3_r2 sat_r2]].
  exists r3. rewrite r1_eq_r2. intuition.
Save.
*)

Lemma sat_leq : forall r1 r2 A,
  sat r1 A -> r1 <: r2 -> sat r2 A.
intros r1 r2 A. generalize r1 r2. clear r1 r2.
induction A; intros; simpl in *.
 (* f_i *)
 trivial.
 (* f_atom *)
 eapply leq_trans; eauto.
 (* f_tensor *)
 destruct H as [r3 [r4 [r3r4_r1 [r2_A1 r3_A2]]]].
 exists r3. exists r4. intuition. eapply leq_trans; eauto.
 (* f_and *)
 intuition eauto.
 (* f_lolli *)
 intros. apply (IHA2 (r1 :*: r') (r2 :*: r')).
  apply H. apply H1.
  apply combine_order. apply H0. apply leq_refl. reflexivity.
 (* f_bang *)
 destruct H as [r' [r'_r1 sat_r']].
 exists r'. intuition. eapply leq_trans; eauto.
Save.

Lemma nat_dec : forall (n:nat), n=0%nat\/(exists m, n = S m).
intros. destruct n.
 left. reflexivity.
 right. exists n. reflexivity.
Save.

Require Omega.

Lemma not_in_mem_false : forall n s,
  ~ (VarSet.In n s) -> VarSet.mem n s = false.
intros.
compare (VarSet.mem n s) true; intros.
 elimtype False. apply H. apply VarSet.mem_2. assumption.
 rewrite (not_true_is_false _ n0). reflexivity.
Save.
Implicit Arguments not_in_mem_false [n s].

Lemma not_mem : forall n m,
  n <> m ->
  VarSet.mem m (VarSet.singleton n) = false.
intros.
apply not_in_mem_false.
unfold not. intros. apply H. apply VarSet.singleton_1. assumption.
Save.

Lemma sat_singleton : forall r G m n A,
  sat r (context_to_formula G m (VarSet.singleton (n+m))) ->
  nth_error G n = Some A ->
  sat r A.
intros. generalize m n H H0. clear m n H H0.
induction G; intros.
 destruct n; discriminate.
 destruct (nat_dec n) as [n_is_0 | [n' n_is_Sn']].
  (* this is the correct one *)
  subst. inversion H0. subst.
  simpl in H. rewrite VarSet.mem_1 in H.
   simpl in H. destruct H as [r1 [r2 [r1r2_r [sat_r1 _]]]]. eapply sat_leq. apply sat_r1. eapply right_weaken. apply r1r2_r.
   apply VarSet.singleton_2. change (VarSet.E.eq m m) with (m = m). apply refl_equal. (* BUG *)
  (* step on *)
  subst. simpl in H0. simpl in H. rewrite not_mem in H.
   eapply IHG.
    replace (S (n' + m)) with (n' + (S m)) in H.
     apply H.
     omega.
    assumption.
   omega.
Save.

Lemma sep_mem : forall m U1 U2,
  VarSet.In m U1 ->
  VarSet.Empty (VarSet.inter U1 U2) ->
  VarSet.mem m U2 = false.
intros. destruct (SYN.VarSetProps.In_dec m U2) as [in_2 | not_in_2].
 (* contradiction *)
 assert (VarSet.In m (VarSet.inter U1 U2)). apply VarSet.inter_3; assumption.
 elimtype False. apply (H0 _ H1).
 (* not_there *)
 apply not_in_mem_false. assumption.
Save.
Implicit Arguments sep_mem [m U1 U2].

Lemma sep_mem_s : forall m U1 U2,
  VarSet.In m U2 ->
  VarSet.Empty (VarSet.inter U1 U2) ->
  VarSet.mem m U1 = false.
intros.
apply (sep_mem (U1:=U2) (U2:=U1) H).
rewrite SYN.VarSetProps.inter_sym.
assumption.
Save.
Implicit Arguments sep_mem_s [m U1 U2].

Lemma not_in_union : forall x U1 U2,
  ~(VarSet.In x (VarSet.union U1 U2)) ->
  ~(VarSet.In x U1) /\ ~(VarSet.In x U2).
intros.
destruct (SYN.VarSetProps.In_dec x U1) as [in_1 | not_in_1].
 elimtype False. apply H. apply VarSet.union_2. assumption. 
 destruct (SYN.VarSetProps.In_dec x U2) as [in_2 | not_in_2].
  elimtype False. apply H. apply VarSet.union_3. assumption.
  auto.
Save.
Implicit Arguments not_in_union [x U1 U2]. 

Lemma sat_split : forall r G m U1 U2,
  VarSet.Empty (VarSet.inter U1 U2) ->
  sat r (context_to_formula G m (VarSet.union U1 U2)) ->
  exists r1, exists r2,
    r1 :*: r2 <: r /\ sat r1 (context_to_formula G m U1) /\ sat r2 (context_to_formula G m U2).
intros r G m U1 U2 sep. generalize r m. clear r m. induction G; intros.
 (* base case *)
 simpl. exists e. exists e. intuition. rewrite e_combine_r. apply e_bottom.
 (* step case *)
 simpl in *.
 destruct (SYN.VarSetProps.In_dec m (VarSet.union U1 U2)) as [is_in | isnt_in].
  (* we included this position originally *)
  rewrite (VarSet.mem_1 is_in) in H. simpl in H. destruct H as [r1 [r2 [r1r2_r [sat_r1_a sat_r2_rest]]]].
  destruct (VarSet.union_1 is_in) as [in_1 | in_2].
   (* it was in U1 *)
   rewrite (VarSet.mem_1 in_1). 
   rewrite (sep_mem in_1 sep).
   destruct (IHG _ _ sat_r2_rest) as [r1' [r2' [r1'r2'_r2 [r1'_U1 r2'_U2]]]].
   exists (r1 :*: r1'). exists r2'. intuition.
    rewrite <- combine_assoc. eapply leq_trans. 
     apply combine_order.
      apply leq_refl. reflexivity.
      apply r1'r2'_r2.
     apply r1r2_r.
    exists r1. exists r1'. intuition. 
   (* it was in U2 *)
   rewrite (VarSet.mem_1 in_2). 
   rewrite (sep_mem_s in_2 sep).
   destruct (IHG _ _ sat_r2_rest) as [r1' [r2' [r1'r2'_r2 [r1'_U1 r2'_U2]]]].
   exists r1'. exists (r1 :*: r2'). intuition.
    rewrite combine_assoc. rewrite (combine_symm r1' r1). rewrite <- combine_assoc.
    eapply leq_trans. 
     apply combine_order.
      apply leq_refl. reflexivity.
      apply r1'r2'_r2.
     apply r1r2_r.
    exists r1. exists r2'. intuition. 
  (* we didn't originally include this position *)
  destruct (not_in_union isnt_in) as [not_in_1 not_in_2].
  rewrite (not_in_mem_false not_in_1).
  rewrite (not_in_mem_false not_in_2).
  rewrite (not_in_mem_false isnt_in) in H.
  auto.
Save.
Implicit Arguments sat_split [r G m U1 U2].

Lemma shift_step_union : forall S S2 a,
  VarSet.Equal (shift_step a (VarSet.union S2 S)) (VarSet.union (shift_step a S2) S).
intros. destruct a; simpl; auto with set.
Save.

Lemma shift_step_morphism : forall a S1 S2,
  VarSet.Equal S1 S2 ->
  VarSet.Equal (shift_step a S1) (shift_step a S2).
intros. destruct a.
 assumption.
 simpl. setoid_replace S1 with S2.
  reflexivity.
  assumption.
Save.

Definition fold_left_shift := fold_left (fun a b => shift_step b a).

Add Morphism fold_left_shift : fold_left_morphism.
intro l. induction l; intros; simpl.
 assumption.
 apply IHl. apply shift_step_morphism. assumption.
Save.

Lemma fold_shift_step_union : forall l S S2,
  VarSet.Equal (fold_left (fun a b => shift_step b a) l (VarSet.union S2 S))
               (VarSet.union (fold_left (fun a b => shift_step b a) l S2) S).
intros l. induction l; intros; simpl.
 unfold VarSet.Equal. split; intro; assumption.
 setoid_rewrite <- IHl. apply fold_left_morphism. auto. apply shift_step_union.
Save. 

Lemma fold_shift_step_only_add : forall m l S,
  VarSet.In m (fold_left (fun a b => shift_step b a) l S) ->
  ~(VarSet.In m S) ->
  VarSet.In m (fold_left (fun a b => shift_step b a) l VarSet.empty).
intros m l S is_in m_nin_S.
fold fold_left_shift in is_in.
setoid_replace S with (VarSet.union VarSet.empty S) in is_in; [|auto with set].
rewrite fold_shift_step_union in is_in.
destruct (VarSet.union_1 is_in).
 assumption.
 contradiction.
Save.

Lemma shift_prop : forall m U,
  VarSet.In m (shift_down U) ->
  VarSet.In (S m) U.
intros. unfold shift_down in H.
rewrite VarSet.fold_1 in H.
apply VarSet.elements_2.
induction (VarSet.elements U).
 simpl in H. elimtype False. apply (VarSet.empty_1 H).
 simpl in H. destruct (nat_dec a) as [is_0 | [x a_is_Sx]].
  subst. auto.
  subst. destruct (Peano_dec.eq_nat_dec x m).
   subst. apply InA_cons_hd. reflexivity.
   apply InA_cons_tl. apply IHl. eapply fold_shift_step_only_add.
    apply H.
    simpl. rewrite <- SYN.VarSetProps.singleton_equal_add. unfold not. intros. apply n. apply VarSet.singleton_1. assumption.
Save.

Lemma shift_prop_2 : forall m U,
  VarSet.In (S m) U ->
  VarSet.In m (shift_down U).
intros. unfold shift_down.
rewrite VarSet.fold_1.
set (H':=VarSet.elements_1 H). generalize H'. clear H H'. intro H.
induction (VarSet.elements U).
 inversion H.
 inversion H; subst.
  simpl. destruct (nat_dec a) as [is_0 | [x a_is_Sx]]; subst.
   discriminate.
   simpl. setoid_replace (fold_left (fun a b => shift_step b a) l (VarSet.add x VarSet.empty))
                    with (fold_left (fun a b => shift_step b a) l (VarSet.union VarSet.empty (VarSet.singleton x))).
    fold fold_left_shift.
    rewrite fold_shift_step_union.
    apply VarSet.union_3. apply VarSet.singleton_2. apply eq_add_S. symmetry. apply H1.
    apply fold_left_morphism. reflexivity. rewrite <- SYN.VarSetProps.singleton_equal_add. rewrite SYN.VarSetProps.empty_union_1; auto with set.
  simpl. destruct (nat_dec a) as [is_0 | [x a_is_Sx]]; subst.
   simpl. apply IHl. assumption.
   simpl. setoid_replace (fold_left (fun a b => shift_step b a) l (VarSet.add x VarSet.empty))
                    with (fold_left (fun a b => shift_step b a) l (VarSet.union VarSet.empty (VarSet.singleton x))).
    fold fold_left_shift.
    rewrite fold_shift_step_union.
    apply VarSet.union_2. apply IHl. apply H1.
    apply fold_left_morphism. reflexivity. rewrite <- SYN.VarSetProps.singleton_equal_add. rewrite SYN.VarSetProps.empty_union_1; auto with set.
Save.

Lemma sat_shift_aux : forall r m G U,
  sat r (context_to_formula G m (shift_down U)) ->
  sat r (context_to_formula G (S m) U).
intros. generalize r m H. clear r m H. induction G; intros.
 simpl in *. trivial.
 simpl in *. destruct (SYN.VarSetProps.In_dec m (shift_down U)).
  (* it was in the shifted down one *)
  rewrite (VarSet.mem_1 i) in H. rewrite (VarSet.mem_1 (shift_prop _ _ i)).
  simpl in H. destruct H as [r1 [r2 [r1r2_r [sat_r1 sat_r2]]]].
  exists r1. exists r2. intuition.
  (* it wasn't in the shifted down one *)
  rewrite (not_in_mem_false n) in H.
  destruct (SYN.VarSetProps.In_dec (S m) U) as [is_in | isnt_in].
   elimtype False. apply n. apply shift_prop_2. apply is_in.
   rewrite (not_in_mem_false isnt_in). auto.
Save.

Lemma sat_shift : forall r1 r2 G U A,
  sat r2 (context_to_formula G 0 (shift_down U)) ->
  sat r1 A ->
  sat (r1 :*: r2) (context_to_formula (A::G) 0 U).
intros. simpl. destruct (SYN.VarSetProps.In_dec 0%nat U) as [has_0 | no_0].
 (* 0 was in U *)
 rewrite (VarSet.mem_1 has_0). exists r1. exists r2. intuition.
  apply sat_shift_aux. assumption.
 (* 0 wasn't in U *)
 rewrite (not_in_mem_false no_0). eapply sat_leq. 
  apply sat_shift_aux. apply H.
  rewrite <- (e_combine_r r2). apply combine_order.
   apply e_bottom.
   rewrite e_combine_r. apply leq_refl. reflexivity.
Save.

Lemma notin_subset : forall m S1 S2,
  ~(VarSet.In m S2) ->
  VarSet.Subset S1 S2 ->
  ~(VarSet.In m S1).
intros. destruct (SYN.VarSetProps.In_dec m S1).
 elimtype False. auto.
 apply n.
Save.
Implicit Arguments notin_subset [m S1 S2].

Lemma sat_subset : forall r m G U1 U2,
  VarSet.Subset U2 U1 ->
  sat r (context_to_formula G m U1) ->
  sat r (context_to_formula G m U2).
intros r m G U1 U2 U2_ss_U1.
generalize r m. clear r m. induction G; intros.
 (* base case *)
 trivial.
 (* step case *)
 simpl in *. destruct (SYN.VarSetProps.In_dec m U1) as [in_U1 | notin_U1].
  (* is in U1 *)
  rewrite (VarSet.mem_1 in_U1) in H. simpl in H.
  destruct H as [r1 [r2 [r1r2_r [sat_r1 sat_r2]]]].
  destruct (SYN.VarSetProps.In_dec m U2) as [in_U2 | notin_U2].
   (* is in U2 *)
   rewrite (VarSet.mem_1  in_U2). exists r1. exists r2. intuition.
   (* not in U2 *)
   rewrite (not_in_mem_false notin_U2). eapply sat_leq.
    apply IHG. apply sat_r2.
    rewrite <- (e_combine_r r2).
    eapply leq_trans.
     apply combine_order. apply e_bottom. apply leq_refl. reflexivity.
     apply r1r2_r.
  (* not in U1 *)
  rewrite (not_in_mem_false notin_U1) in H.
  rewrite (not_in_mem_false (notin_subset notin_U1 U2_ss_U1)).
  auto.
Save.

Lemma get_from_icontext : forall r G n A,
  nth_error G n = Some A ->
  sat r (f_bang (icontext_to_formula G)) ->
  sat r A.
intros r G n A. generalize r n. clear r n.
induction G; intros.
 (* empty list *)
 destruct n; discriminate.
 (* cons *)
 simpl in *.
 destruct H0 as [r' [r'_r1 [r1 [r2 [r1r2_r [sat_r1 sat_r2]]]]]].
 destruct (nat_dec n) as [n_is_0 | [x n_is_Sx]]; subst; simpl in *.
  (* found here *)
  inversion H. subst.
  eapply sat_leq.
   apply sat_r1.
   eapply leq_trans.
    eapply right_weaken. apply r1r2_r.
    eapply leq_trans. apply bang_unit. assumption.
  (* not found here *)
  eapply sat_leq.
   eapply IHG.
    apply H.
    exists r2. intuition.
     apply bang_order. eapply left_weaken. apply r1r2_r.
   apply r'_r1.
Save.

Lemma context_empty : forall U G m,
  VarSet.Empty U ->
  context_to_formula G m U = f_i.
intros U G m U_empty. generalize m. clear m. induction G; intros.
 reflexivity.
 simpl. rewrite (not_in_mem_false (U_empty m)). auto.
Save.

Lemma combine_resources : forall r1 r2 rI rL r' r,
  rI :*: rL <: r ->
  !r' <: rI ->
  r1 :*: r2 <: rL ->
  !r' :*: r1 :*: (!r' :*: r2) <: r.
intros r1 r2 rI rL r' r rIrL_r r'_rI r1r2_r.
rewrite (combine_symm (!r') r1).
rewrite <- combine_assoc.
rewrite (combine_assoc (!r') (!r')).
rewrite combine_symm. rewrite <- combine_assoc.
eapply leq_trans. 
 apply combine_order.
  apply bang_codup.
  rewrite combine_symm at 1. apply r1r2_r.
 eapply leq_trans.
  apply combine_order. apply r'_rI. apply leq_refl. reflexivity.
  apply rIrL_r.
Save.

Lemma soundness : forall r Gi G t A U,
  prf Gi G t A U ->
  sat r (f_tensor (f_bang (icontext_to_formula Gi)) (context_to_formula G 0 U)) ->
  sat r A.
intros r Gi G t A U prf_deriv. generalize r. clear r.
induction prf_deriv; intros.
 (* prf_ivar *)
 destruct H1 as [rI [rL [rIrL_r [sat_I sat_L]]]].
 eapply sat_leq.
  eapply get_from_icontext.
   apply H.
   simpl. apply sat_I.
  eapply right_weaken. apply rIrL_r.
 (* prf_lvar *)
 destruct H1 as [rI [rL [rIrL_r [sat_I sat_L]]]].
 eapply sat_leq.
  eapply sat_singleton.
   replace n with (n+0) in H0. rewrite H0 in sat_L. apply sat_L. omega.
   apply H.
  eapply left_weaken. apply rIrL_r. 
 (* prf_i_intro *)
 simpl. trivial.
 (* prf_tensor_intro *)
 destruct H1 as [rI [rL [rIrL_r [sat_I sat_L]]]]. fold sat in *.
 destruct sat_I as [r' [r'_rI sat_r']].
 rewrite H0 in sat_L.
 destruct (sat_split H sat_L) as [r1 [r2 [r1r2_r [sat_r1 sat_r2]]]].
 exists (!r' :*: r1). exists (!r' :*: r2). intuition.
  eapply combine_resources; eauto.
  apply IHprf_deriv1. exists (!r'). exists r1. intuition.
   exists r'. intuition.
  apply IHprf_deriv2. exists (!r'). exists r2. intuition.
   exists r'. intuition.
 (* prf_tensor_elim *)
 apply IHprf_deriv2.
 destruct H1 as [rI [rL [rIrL_r [sat_rI sat_rL]]]]. fold sat in *.
 rewrite H0 in sat_rL.
 destruct sat_rI as [r' [r'_rI sat_r']].
 destruct (sat_split H sat_rL) as [r1 [r2 [r1r2_r [sat_r1 sat_r2]]]].
 simpl in IHprf_deriv1. destruct (IHprf_deriv1 (!r' :*: r1)) as [rA [rB [rArB_r1 [sat_rA sat_rB]]]].
  exists (!r'). exists r1. intuition.
   exists r'. intuition.
  exists (!r'). exists (rA :*: (rB :*: r2)). intuition.
   rewrite (combine_assoc rA rB r2). rewrite combine_assoc. eapply leq_trans.
    apply combine_order. eapply leq_trans. 
     apply combine_order.
      apply leq_refl. reflexivity.
      apply rArB_r1.
     rewrite combine_assoc at 1. apply combine_order.
      apply bang_codup.
      apply leq_refl. reflexivity.
     apply leq_refl. reflexivity.
    rewrite <- combine_assoc. eapply leq_trans.
     apply combine_order. apply r'_rI. apply r1r2_r.
     apply rIrL_r.
   exists r'. intuition.
   apply sat_shift.
    apply sat_shift; assumption.
    assumption.
 (* prf_and_intro *)
 destruct H0 as [rI [rL [rIrL_r [sat_rI sat_rL]]]].
 rewrite H in sat_rL. 
 simpl. split.
  apply IHprf_deriv1. exists rI. exists rL. intuition. eapply sat_subset. eapply SYN.VarSetProps.union_subset_1. apply sat_rL.
  apply IHprf_deriv2. exists rI. exists rL. intuition. eapply sat_subset. eapply SYN.VarSetProps.union_subset_2. apply sat_rL.
 (* prf_and_elim_1 *)
 simpl in *. destruct (IHprf_deriv r H). assumption.
 (* prf_and_elim_2 *)
 simpl in *. destruct (IHprf_deriv r H). assumption.
 (* prf_lolli_intro *)
 destruct H0 as [rI [rL [rIrL_r [sat_rI sat_rL]]]].
 rewrite H in sat_rL.
 simpl. intros. 
 apply IHprf_deriv. exists rI. exists (r' :*: rL). intuition.
  rewrite (combine_symm r' rL). rewrite combine_assoc. apply combine_order.
   assumption.
   apply leq_refl. reflexivity.
  apply sat_shift; assumption.
 (* prf_lolli_elim *)
 rewrite H0 in H1.
 destruct H1 as [rI [rL [rIrL_r [sat_rI sat_rL]]]].
 destruct sat_rI as [r' [r'_rI sat_r']].
 destruct (sat_split H sat_rL) as [r1 [r2 [r1r2_r [sat_r1 sat_r2]]]].
 eapply sat_leq.
  simpl in IHprf_deriv1. eapply IHprf_deriv1.
   exists (!r'). exists r1. intuition.
    apply leq_refl. reflexivity.
    exists r'. intuition.
   apply IHprf_deriv2. exists (!r'). exists r2. intuition.
    apply leq_refl. reflexivity.
    exists r'. intuition.
  eapply combine_resources; eauto.
 (* prf_bang_intro *)
 rewrite context_empty in IHprf_deriv; [|assumption].
 destruct H0 as [rI [rL [rIrL_r [sat_rI sat_rL]]]].
 destruct sat_rI as [r' [r'_rI sat_r']].
 exists (!r'). split.
  eapply leq_trans.
   apply bang_mult.
   rewrite <- (r_combine_e (!r')). eapply leq_trans.
    apply combine_order. apply r'_rI. apply e_bottom.
    apply rIrL_r.
  apply IHprf_deriv. exists (!r'). exists e. intuition.
   rewrite r_combine_e. apply leq_refl. reflexivity.
   exists r'. intuition. 
   simpl. trivial.
 (* prf_bang_elim *)
 apply IHprf_deriv2.
 rewrite H0 in H1.
 destruct H1 as [rI [rL [rIrL_r [sat_rI sat_rL]]]].
 destruct sat_rI as [r' [r'_rI sat_r']].
 destruct (sat_split H sat_rL) as [r1 [r2 [r1r2_r [sat_r1 sat_r2]]]].
 simpl in IHprf_deriv1. destruct (IHprf_deriv1 (!r' :*: r1)) as [rA [rA_r sat_rA]].
  exists (!r'). exists r1. intuition.
   exists r'. intuition.
  exists (!(rA :*: r')). exists r2. intuition.
   rewrite bang_combine. rewrite <- combine_assoc. eapply leq_trans.
    apply combine_order.
     apply rA_r. apply leq_refl. reflexivity.
     eapply combine_resources; eauto.
   exists (rA :*: r'). intuition.
    exists rA. exists r'. intuition.
 (* prf_axiom *)
 apply axioms_sound. apply IHprf_deriv. apply H.
 (* prf_let *)
 rewrite H in *. rewrite H1 in H2.
 destruct H2 as [rI [rL [rIrL_r [sat_rI sat_rL]]]].
 destruct sat_rI as [r' [r'_rI sat_r']].
 destruct (sat_split H0 sat_rL) as [r1 [r2 [r1r2_r [sat_r1 sat_r2]]]].
 eapply sat_leq.
  apply IHprf_deriv2.
   exists (!r'). exists (!r':*:rL). intuition.
    apply leq_refl. reflexivity.
    exists r'. intuition.
 apply sat_leq with (r1:=(!r' :*: r1) :*: r2).
  apply sat_shift. assumption.
  apply IHprf_deriv1.
  exists (!r'). exists r1. intuition.
  exists r'. intuition.
  rewrite <- combine_assoc. apply combine_order.
    apply leq_refl. reflexivity.
    assumption.
 rewrite combine_assoc.
 eapply leq_trans. apply combine_order. eapply leq_trans. apply bang_codup. apply r'_rI.
 apply leq_refl. reflexivity.
 assumption.
Save.

Lemma single_soundness : forall r A B t U,
  sat r A ->
  prf nil (A::nil) t B U ->
  sat r B.
intros r A B t U sat_r_A prf_A_B. eapply soundness.
 apply prf_A_B.
 simpl.
 exists e. exists r. intuition.
  rewrite e_combine_r. apply leq_refl. reflexivity.
  exists e. intuition. apply leq_refl. apply bang_e.
 destruct (SYN.VarSetProps.In_dec 0%nat U) as [in_U | notin_U].
  (* the evidence was used by the proof *)
  rewrite (VarSet.mem_1 in_U).
  exists r. exists e. simpl. intuition.
   rewrite r_combine_e. apply leq_refl. reflexivity.
  (* the evidence was not used by the proof *)
  rewrite (not_in_mem_false notin_U). simpl. trivial.
Save.

Lemma implies_soundness : forall r A B,
  sat r A ->
  implies A B ->
  sat r B.
intros r A B r_A A_implies_B.
destruct A_implies_B as [t [U prf_ok]]. 
eapply single_soundness; eassumption.
Save.

Lemma res_formula : forall re,
  sat (res_parse re) (resexpr_to_formula re).
Proof.
  unfold resexpr_to_formula.
  intro.
  assert (sat e f_i) by (simpl;trivial).
  apply sat_leq with (r1:=e:*:res_parse re).
  generalize e f_i H. clear H.

  induction re.
    intros. unfold res_parse. simpl. eapply sat_leq. apply H. rewrite r_combine_e. apply leq_refl. reflexivity.
    intros. unfold r_may. destruct a as [[|] c].
     simpl. destruct (r_new c) as [rc|] _eqn: req. apply sat_leq with (r1:=(r :*: !rc) :*: res_parse re).
      apply IHre. simpl. exists r. exists (!rc). repeat split.
        apply leq_refl. reflexivity.
        assumption.
        destruct (r_new_match _ _ req) as [a [req' aeq]]. rewrite req'. simpl. exists rc. split.
         apply leq_refl. reflexivity.
         apply RA.leq_refl. apply RA.eq_symm. rewrite aeq. reflexivity.
      apply leq_refl. apply eq_symm. apply combine_assoc.
     rewrite (r_new_empty _ req). apply IHre. simpl. exists r. exists e. intuition.
      rewrite r_combine_e. apply leq_refl. reflexivity.

     simpl. destruct (r_new c) as [rc|] _eqn: req.
      apply sat_leq with (r1:=(r :*: rc) :*: res_parse re).
       apply IHre. simpl. exists r. exists rc. intuition.
        destruct (r_new_match _ _ req) as [a [req' aeq]]. rewrite req'. simpl. rewrite aeq. apply leq_refl. reflexivity.
      apply leq_refl. apply eq_symm. apply combine_assoc.
       apply IHre. simpl. exists r. exists e. intuition.
        apply leq_refl. rewrite r_combine_e. reflexivity.
        rewrite (r_new_empty _ req). simpl. trivial. 

   apply leq_refl. rewrite e_combine_r. reflexivity.
Qed.

End MkILLSemantics.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "." "ILL")
   End:
   *)
















Require Import BasicMachineTypes.
Require Import List.
Require Import Wf_nat.
Require Omega.
Require Import Arith.
Require Store.

Module FinitePoset (N : NAMETYPE).

(* Represent a poset by a list of pairs that are related. The real poset is the reflexive transitive closure of this *)

Module S := Store.MkStore N N.

Definition t:=S.t.

Fixpoint leq_aux (p:t) (P:S.wf_removals p) (a b:N.t) {struct P} : bool :=
  match N.eq_dec a b with
  | left _ => true
  | right _ =>
     match S.lookup_informative p a with
     | inleft (exist x a_exists) =>
        let P' := S.wf_removals_inv a_exists P in
          leq_aux (S.remove a p) P' x b 
     | inright _ =>
        false
     end
  end.

Definition leq := fun p => leq_aux p (S.all_wf_removals p).

Inductive leq_prop : t -> N.t -> N.t -> Prop :=
| leq_prop_refl  : forall p a, leq_prop p a a
| leq_prop_rem_trans : forall p a b c,
    S.lookup p a = Some b ->
    leq_prop (S.remove a p) b c ->
    leq_prop p a c.

Lemma leq_aux_sound : forall p P a b, leq_aux p P a b = true -> leq_prop p a b.
intros p P. elim P using S.wf_removals_ind2; intros.

simpl in H. destruct (N.eq_dec a b). 
 subst. apply leq_prop_refl.
 destruct (S.lookup_informative S.empty a) as [[o o_exists] | no_o].
  clear H. rewrite S.lookup_empty in o_exists. discriminate.
  discriminate.

simpl in H0. destruct (N.eq_dec a b).
 subst. apply leq_prop_refl.
 destruct (S.lookup_informative s a). 
  destruct s0. eapply leq_prop_rem_trans. 
   apply e.
   apply (H _ _ _ _ _ H0).
  discriminate.
Save.

Lemma leq_sound : forall p a b, leq p a b = true -> leq_prop p a b.
intros. unfold leq in H. eapply leq_aux_sound. apply H.
Save.

Lemma leq_aux_complete : forall p P a b, leq_prop p a b -> leq_aux p P a b = true.
intros p P. elim P using S.wf_removals_ind2; intros.

simpl. destruct (N.eq_dec a b).
 reflexivity.
 inversion H. contradiction. rewrite S.lookup_empty in H0. discriminate.

simpl. inversion H0; subst.
 destruct (N.eq_dec b b).
  reflexivity.
  elimtype False. apply n. reflexivity.
 destruct (N.eq_dec a b).
  reflexivity.
  destruct (S.lookup_informative s a).
   destruct s0. rewrite e in H1. inversion H1. generalize e. clear e. rewrite H4. intro. 
   apply (H _ b0 e _ _ H2).
   rewrite e in H1. discriminate.
Save.

Lemma leq_complete : forall p a b, leq_prop p a b -> leq p a b = true.
intros. unfold leq. apply leq_aux_complete. assumption.
Save.

Section holds_for_list.

Hypothesis A : Set.
Hypothesis P : A -> Prop.

Inductive holds_for_list : list A -> Prop :=
| holds_for_nil  : holds_for_list nil
| holds_for_cons : forall a l, P a -> holds_for_list l -> holds_for_list (a::l).

End holds_for_list.

Section Soundness.

Hypothesis LEQ : N.t -> N.t -> Prop.
Hypothesis LEQ_trans : forall a b c, LEQ a b -> LEQ b c -> LEQ a c.
Hypothesis LEQ_refl : forall a, LEQ a a.

Definition all_LEQ := fun p =>
  forall a b, S.lookup p a = Some b -> LEQ a b.

Lemma remove_preserve_all_LEQ : forall p x,
  all_LEQ p -> all_LEQ (S.remove x p).
unfold all_LEQ. intros. 
apply H. eapply S.remove_lookup_3. apply H0.
Save.

Lemma leq_prop_LEQ : forall p a b, all_LEQ p -> leq_prop p a b -> LEQ a b.
intros. induction H0. 
 apply LEQ_refl.
 eapply LEQ_trans. 
  apply (H _ _ H0). 
  apply IHleq_prop. apply remove_preserve_all_LEQ. apply H.
Save.

Lemma leq_LEQ : forall p a b, all_LEQ p -> leq p a b = true -> LEQ a b.
intros. unfold leq in H0. eapply leq_prop_LEQ. 
 apply H. 
 eapply leq_aux_sound. apply H0. 
Save.

End Soundness.

Lemma leq_prop_remove : forall p a b x, leq_prop (S.remove x p) a b -> leq_prop p a b.
intros. 
set (p':=S.remove x p) in *. set (e:=refl_equal p' : p' = S.remove x p). 
generalize p' H e. clear p' H e. intros p' H. generalize p. clear p.
induction H; intros.
 apply leq_prop_refl.
 rewrite e in H. 
 eapply leq_prop_rem_trans. 
  eapply S.remove_lookup_3. apply H. 
  apply IHleq_prop. rewrite e. apply S.commute_remove.
Save.

Lemma trans_helper : forall a p c c0, leq_prop p c c0 ->
     leq_prop (S.remove a p) c c0
  \/ (exists b, S.lookup p a = Some b /\ leq_prop (S.remove a p) b c0).
intros. induction H.
 left. apply leq_prop_refl.
 destruct (N.eq_dec a a0).
  subst. right. exists b. split; assumption.
  destruct IHleq_prop.
   left. eapply leq_prop_rem_trans. 
    apply S.remove_lookup_4. apply H. assumption.
    rewrite S.commute_remove. apply H1.
   right. destruct H1. destruct H1. exists x. split.
    eapply S.remove_lookup_3. apply H1.
    eapply (leq_prop_remove (S.remove a p) x c a0). rewrite S.commute_remove. apply H2.
Save.

Lemma leq_prop_trans : forall p a b c, leq_prop p a b -> leq_prop p b c -> leq_prop p a c.
intros p a b c H. generalize c. clear c. induction H; intros.
 assumption.
 eapply leq_prop_rem_trans. 
  apply H.
  destruct (trans_helper a p c c0 H1).
   apply IHleq_prop. assumption.
   destruct H2. destruct H2. rewrite H2 in H. inversion H. subst. assumption. 
Save.  

Lemma leq_refl : forall p a, leq p a a = true.
intros. unfold leq. apply leq_aux_complete. apply leq_prop_refl.
Save.

(* 'and' works by assuming that everything has at most one parent,
   getting the transitive list of parents of both and finding the least common entry *)

Definition list_informative : forall (A:Set) (l:list A), { a : A & { l' : list A | l = a::l' } }+{l = nil}.
intros. destruct l.
 right. reflexivity.
 left. exists a. exists l. reflexivity.
Defined.
Implicit Arguments list_informative [A].

Lemma not_nil : forall (A:Set) (l:list A) a l', l = a::l' -> l <> nil.
intros. unfold not. intro. subst. discriminate.
Save.
Implicit Arguments not_nil [A l a l'].

Fixpoint get_all_parents (p:t) (P:S.wf_removals p) (a:N.t) {struct P} : list N.t :=
  match S.lookup_informative p a with
  | inleft (exist b a_exists) =>
     let P' := S.wf_removals_inv a_exists P in
      a::get_all_parents (S.remove a p) P' b
  | inright _ => a::nil
  end.

Definition all_leq_prop := fun p a => holds_for_list N.t (leq_prop p a).


Lemma holds_for_list_implies : forall (A:Set) (P1 P2:A->Prop) l, (forall a, P1 a -> P2 a) -> 
  holds_for_list A P1 l ->
  holds_for_list A P2 l.
intros. induction H0. 
 apply holds_for_nil.
 apply holds_for_cons; auto. 
Save.

Lemma get_all_parents_leq_prop : forall p P a l,
  get_all_parents p P a = l -> all_leq_prop p a l.
intros p P. elim P using S.wf_removals_ind2; intros.

simpl in H. destruct (S.lookup_informative S.empty a) as [[o o_exists] | no_o].
 clear H. rewrite S.lookup_empty in o_exists. discriminate.
 subst. unfold all_leq_prop. apply holds_for_cons. 
  apply leq_prop_refl.
  apply holds_for_nil.

simpl in H0. unfold all_leq_prop.
destruct (S.lookup_informative s a). 
 destruct s0. 
 subst. apply holds_for_cons.
  apply leq_prop_refl.
  eapply holds_for_list_implies.
   intros. eapply leq_prop_rem_trans. apply e. apply H0. 
   apply (H a x e x _ (refl_equal _)).
 subst. apply holds_for_cons. 
  apply leq_prop_refl.
  apply holds_for_nil.
Save.

Fixpoint find_first_also_in_other_list (l:list N.t) (l2:list N.t) {struct l} : option N.t :=
  match l with
  | nil => None
  | x::l => if In_dec N.eq_dec x l2 then Some x else find_first_also_in_other_list l l2
  end.

Definition and : t -> N.t -> N.t -> option N.t :=
  fun p a b =>
  let a_parents := get_all_parents p (S.all_wf_removals p) a in
  let b_parents := get_all_parents p (S.all_wf_removals p) b in
   find_first_also_in_other_list a_parents b_parents.

Lemma and_aux_p1 : forall p x xs ys z,
  all_leq_prop p x xs ->
  find_first_also_in_other_list xs ys = Some z ->
  leq_prop p x z.
intros. induction xs. 
 discriminate.
 simpl in H0. inversion H. subst. destruct (In_dec N.eq_dec a ys). 
  inversion H0. subst. assumption.
  auto. 
Save. 

Lemma and_aux_p2_aux : forall p x ys z,
  all_leq_prop p x ys ->
  In z ys -> leq_prop p x z.
intros. induction ys.
 inversion H0. 
 inversion H. subst. inversion H0. 
  subst. assumption. 
  auto. 
Save. 

Lemma and_aux_p2 : forall p x xs ys z,
  all_leq_prop p x ys ->
  find_first_also_in_other_list xs ys = Some z ->
  leq_prop p x z.
intros. induction xs. 
 inversion H0. 
 simpl in H0. destruct (In_dec N.eq_dec a ys). 
  inversion H0. subst. eapply and_aux_p2_aux; eauto.
  auto.
Save.

Lemma and_p1 : forall p a b c,
  and p a b = Some c -> leq_prop p a c.
intros. unfold and in H. unfold leq. eapply and_aux_p1. 
 eapply get_all_parents_leq_prop. reflexivity. 
 apply H.
Save.

Lemma and_p2 : forall p a b c,
  and p a b = Some c -> leq_prop p b c.
intros. unfold and in H. unfold leq. eapply and_aux_p2. 
 eapply get_all_parents_leq_prop. reflexivity. 
 apply H.
Save.


End FinitePoset.










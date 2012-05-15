Require Import List.
Require OrderedType.
Require FMapInterface.
Require BoolExt.
Require Import Setoid.

Module MakeOverlay (M : FMapInterface.S).

Section A.

Hypothesis A : Type.

Lemma key_eq_dec : forall (k k':M.key), {M.E.eq k k'}+{~M.E.eq k k'}.
intros. destruct (M.E.compare k k').
 right. apply M.E.lt_not_eq. assumption.
 left. assumption.
 right. unfold not. intro. refine (M.E.lt_not_eq l _). apply M.E.eq_sym. assumption.
Save.

Definition overlay : M.t A -> M.t A -> M.t A :=
 fun specs' specs =>
  M.fold (fun mdesc spec specs' => if M.mem mdesc specs' then specs' else M.add mdesc spec specs') specs specs'.

Lemma mem_3 : forall x y (m : M.t A),
 M.E.eq x y -> M.In x m -> M.In y m.
intros x y m x_eq_y [e m_x_e]. exists e. eauto using M.MapsTo_1.
Save.
Implicit Arguments mem_3 [x y m].

Lemma add_4 : forall k1 k2 e e' (m:M.t A),
 M.E.eq k1 k2 -> M.MapsTo k1 e (M.add k2 e' m) -> e = e'.
intros.
assert (M.find k1 (M.add k2 e' m) = Some e) by auto using M.find_1.
assert (M.find k1 (M.add k2 e' m) = Some e') by auto using M.find_1, M.add_1, M.E.eq_sym.
congruence.
Save.

Lemma overlay_law1 : forall md sp specs' specs,
 M.MapsTo md sp (overlay specs' specs) ->
 M.MapsTo md sp specs' \/ (~M.In md specs' /\ M.MapsTo md sp specs).
intros md sp specs' specs.
unfold overlay. rewrite M.fold_1.
setoid_replace (M.MapsTo md sp specs) with (SetoidList.InA (M.eq_key_elt (elt:=A)) (md,sp) (M.elements specs)).
set (l:=M.elements specs).
generalize l specs'. clear specs' l. induction l as [|[key elt] l]; intros; simpl in *.
 left. assumption.
 destruct (BoolExt.bool_informative (M.mem key specs')) as [mem_res | mem_res]; rewrite mem_res in H.
  destruct (IHl _ H); intuition.
  destruct (IHl _ H) as [in_specs' | [not_in_specs' in_l]].
   destruct (key_eq_dec key md).
    right. split.
     unfold not. intros.  rewrite (M.mem_1 (mem_3 (M.E.eq_sym e) H0)) in mem_res. discriminate.
     assert (sp=elt). eapply add_4. apply M.E.eq_sym. apply e. apply in_specs'. subst. constructor. unfold M.eq_key_elt. simpl. intuition.
    left. eapply M.add_3. apply n. apply in_specs'.
   destruct (key_eq_dec key md).
    subst. elimtype False. apply not_in_specs'. exists elt. apply M.add_1. assumption.
    right. split.
     unfold not. intro. apply not_in_specs'. destruct H0. exists x. apply M.add_2. apply n. apply H0.
     apply SetoidList.InA_cons_tl. apply in_l.
split. apply M.elements_1. apply M.elements_2.
Save.

Lemma lt_lelist : forall l k k',
  Sorting.lelistA (M.lt_key (elt:=A)) k l ->
  M.lt_key k' k ->
  Sorting.lelistA (M.lt_key (elt:=A)) k' l.
intros. inversion H.
 constructor.
 constructor. destruct k. destruct b. destruct k'. unfold M.lt_key in *. simpl in *. eauto using M.E.lt_trans.
Save.

Lemma in_sorted_contr : forall key elt1 elt2 l,
 Sorting.sort (@M.lt_key A) l ->
 Sorting.lelistA (@M.lt_key A) (key,elt2) l ->
 SetoidList.InA (@M.eq_key_elt A) (key,elt1) l -> False.
intros key elt1 elt2. 
induction l as [|[key' elt'] l]; intros.
 inversion H1.
 inversion H1; subst.
  inversion H3. simpl in *. subst. clear H1 H3.
   inversion H0. unfold M.lt_key in H3. simpl in H3.
   refine (M.E.lt_not_eq H3 _). assumption.
  inversion H. apply IHl. 
   assumption.
   eapply lt_lelist. apply H6. inversion H0. assumption.
   assumption.
Save.

Lemma InA_eq : forall x y l e,
 M.E.eq x y ->
 SetoidList.InA (@M.eq_key_elt A) (x,e) l ->
 SetoidList.InA (@M.eq_key_elt A) (y,e) l.
intros. induction H0.
 constructor. inversion H0. destruct y0. simpl in *. split; eauto using M.E.eq_trans.
 auto using SetoidList.InA_cons_tl.
Save.

Lemma elements_functional : forall l x y e e',
 M.E.eq x y ->
 Sorting.sort (@M.lt_key A) l ->
 SetoidList.InA (@M.eq_key_elt A) (x,e) l ->
 SetoidList.InA (@M.eq_key_elt A) (y,e') l ->
 e = e'.
induction l as [|[key elt] l]; intros.
 inversion H1.
 inversion H1; subst.
  inversion H2; subst. 
   inversion H4. inversion H5. simpl in *. subst. reflexivity.
   inversion H4. simpl in *. subst. inversion H0.
    elimtype False. eapply in_sorted_contr. apply H8. apply H9. eapply InA_eq.
     eapply M.E.eq_trans. apply M.E.eq_sym. apply H. apply H3. apply H5.
  inversion H1; subst.
   inversion H5. simpl in *. subst. inversion H0. elimtype False. eapply in_sorted_contr; eauto.
    eapply InA_eq; eassumption.
   inversion H0. inversion H2. subst. elimtype False. eapply in_sorted_contr; eauto.
    eapply InA_eq. inversion H10. simpl in *. eapply M.E.eq_trans. apply H. apply H3. apply H4. 
    eauto.
Save.

Lemma overlay_law2 : forall md sp specs' specs,
 M.MapsTo md sp specs' \/ (~M.In md specs' /\ M.MapsTo md sp specs) ->
 M.MapsTo md sp (overlay specs' specs).
intros md sp specs' specs.
unfold overlay. rewrite M.fold_1.
setoid_replace (M.MapsTo md sp specs) with (SetoidList.InA (M.eq_key_elt (elt:=A)) (md,sp) (M.elements specs)).
set (l:=M.elements specs).
assert (X:Sorting.sort (@M.lt_key A) l). unfold l. apply M.elements_3. 
generalize l specs' X. clear specs' l X. induction l as [|[key elt] l]; intros; simpl in *.
 destruct H as [in_specs' | [_ in_nil]]. assumption. inversion in_nil.
 apply IHl.
  inversion X. assumption.
  destruct (BoolExt.bool_informative (M.mem key specs')) as [mem_res | mem_res]; rewrite mem_res.
   destruct H as [in_specs' | [not_in_specs in_ke_l]].
    left. assumption.
    destruct (key_eq_dec md key).
     elimtype False. apply not_in_specs. eapply mem_3. apply M.E.eq_sym. apply e. apply M.mem_2. apply mem_res.
     right. split.
      assumption.
      inversion in_ke_l.
       destruct H0. simpl in H0. contradiction.
       assumption.
  destruct H as [in_specs' | [not_in_specs in_ke_l]].
    left. destruct (key_eq_dec key md).
     assert (M.In key specs'). eapply mem_3. apply M.E.eq_sym. apply e. exists sp. apply in_specs'.
      rewrite (M.mem_1 H) in mem_res. discriminate.
     eapply M.add_2. apply n. apply in_specs'.
   destruct (key_eq_dec md key).
    left. 
     assert (SetoidList.InA (M.eq_key_elt (elt:=A)) (md,elt) ((md,elt)::l)). constructor. split; simpl; auto; apply M.E.eq_refl.
     rewrite (elements_functional ((key,elt)::l) key md sp elt); try assumption.
      apply M.add_1. apply M.E.eq_sym. assumption.
      apply M.E.eq_sym. assumption.
      eapply InA_eq. apply e. assumption.
      constructor. split; eauto.
    right. split.
     unfold not. intro. apply not_in_specs. destruct H. exists x. eapply M.add_3. unfold not. intro. apply n. apply M.E.eq_sym. apply H0. apply H.
     inversion in_ke_l.
      inversion H0. simpl in H2. contradiction.
      assumption.
split. apply M.elements_1. apply M.elements_2.
Save.

Lemma overlay_law : forall md sp specs' specs,
 M.MapsTo md sp (overlay specs' specs) <->
  M.MapsTo md sp specs' \/ (~M.In md specs' /\ M.MapsTo md sp specs).
intros. split. 
 apply overlay_law1.
 apply overlay_law2.
Save.

End A.

End MakeOverlay.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "../ill" "ILL" "-R" "." "Verifier")
   End:
   *)

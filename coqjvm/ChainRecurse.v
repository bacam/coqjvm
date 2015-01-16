Require Import FMapInterface.
Require Import List.
Require Import SetoidList.
Require Import Omega.
Require Program.Tactics.
Require Program.Wf.

(** * Fixpoint for non-cyclic chains of lookups in a map. *)

(* First define some results for SetoidList style lists. *)
Section SetoidListExt.
Set Implicit Arguments.

Variable A:Type.
Variable eqA:A->A->Prop.
Variable eqA_dec: forall x y,{eqA x y} + {~ eqA x y}.
Hypothesis eqA_equiv : Equivalence eqA.

Lemma inclA_nil : forall l:list A, inclA eqA l nil -> l = nil.
Proof.
  induction l.
    reflexivity.

    intro inc.
    absurd (InA eqA a nil).
      intro notin.
      inversion notin.

      apply inc.
      apply InA_cons_hd.
      reflexivity.
Qed.

Lemma inclA_cons (l l':list A) (a:A) : inclA eqA (a::l) l' -> inclA eqA l l'.
Proof.
  intros inc a' a'in.
  apply inc.
  simpl.
  right.
  assumption.
Qed.

Lemma inclA_cons_1 (l l':list A) (a:A) : ~ InA eqA a l -> inclA eqA l (a::l') -> inclA eqA l l'.
Proof.
  intros anotinl inc a' a'in.
  pose (a'in' := inc a' a'in).
  clearbody a'in'.
  inversion a'in' as [x y aa'|x y a'inl']. 
    subst x y.
    apply (InA_eqA (l:=l) eqA_equiv aa') in a'in.
    contradiction.

    assumption.
Qed.

Lemma inclA_remove (l l':list A) (a:A) : inclA eqA l l' -> inclA eqA (removeA eqA_dec a l) l'.
Proof.
  intros inc a' a'in.
  apply inc.
  induction l.
    simpl in *.
    assumption.

    simpl (removeA eqA_dec a (a0 :: l)) in *.
    destruct (eqA_dec a a0) as [aa0|].
      apply InA_cons_tl.
      apply IHl; auto.
      apply inclA_cons with (a:=a0).
      assumption.

      inversion a'in as [x y aeqa'|x y a'in']; subst x y.
        apply InA_cons_hd; assumption.

        apply InA_cons_tl.
        apply IHl.
          apply inclA_cons with (a:=a0).
          assumption.

          assumption.
Qed.

Lemma inclA_discard (l l':list A) (a:A) : inclA eqA l (a::l') -> inclA eqA (removeA eqA_dec a l) l'.
Proof.
  intros inc a' a'in.
  induction l.
    inversion a'in.

    simpl in *.
    destruct (eqA_dec a a0).
      apply IHl.
        apply inclA_cons with (a:=a0).
        assumption.

        assumption.

      inversion a'in as [x y a'a0|x y]; subst x y.
        pose (a'ina0l := inc a' (InA_cons_hd (eqA:=eqA) (x:=a') (y:=a0) l a'a0)).
        inversion a'ina0l as [x y eq0|x y]; subst x y.
          contradict n. 
          transitivity a'; auto.
          symmetry; assumption.

          assumption.

        apply IHl.
          apply inclA_cons with (a:=a0).
          assumption.

          assumption.
Qed.

Lemma notinA_remove (l:list A) (a a':A) : ~ InA eqA a l -> ~ InA eqA a (removeA eqA_dec a' l).
Proof.
  intros.
  induction l.
    simpl.
    auto.

    simpl.
    destruct (eqA_dec a' a0).
      apply IHl.
      intro inl.
      destruct H.
      apply InA_cons_tl.
      assumption.

      intro nottrue.
      inversion nottrue as [x y aeqk|x y kinrl]; subst x y.
        destruct H.
        left.
        assumption.

        apply IHl.
        intro inl.
        destruct H; right; assumption.
        assumption.
Qed.

End SetoidListExt.

(* Now define the recursion module based on some finite map. *)

Module ChainRecurse (M : S).

Module KeyFacts := OrderedType.OrderedTypeFacts M.E.
(* Get rid of some of the excess arguments. *)
Lemma InA_eq : forall l x y, M.E.eq x y -> InA M.E.eq x l -> InA M.E.eq y l.
Proof.
  apply InA_eqA.
  apply KeyFacts.eq_equiv.
Qed.
Implicit Arguments InA_eq [l x y].

Section Recursion.

(* First we need the type of objects in the map. *)
Variable elt:Type.

(* Define the termination measure and lemmata. *)
Definition keys (m:M.t elt) : list M.key :=
  map (fst (A:=M.key) (B:=elt)) (M.elements m).

Definition eltsleft (m:M.t elt) (l:list M.key) : nat :=
  List.length (keys m) - List.length l.

Lemma length_remove_1 (l:list M.key) (k:M.key) :
  ~ InA M.E.eq k l -> length l = length (removeA KeyFacts.eq_dec k l).
Proof.
  induction l.
    reflexivity.

    intros notin.
    simpl.
    destruct (KeyFacts.eq_dec k a).
      destruct notin.
      left.
      assumption.

      simpl.
      f_equal.
      apply IHl.
      intro.
      destruct notin.
      right.
      assumption.
Qed.

Lemma length_remove (l:list M.key) (k:M.key) :
  NoDupA M.E.eq l -> InA M.E.eq k l ->
  length l = S (length (removeA KeyFacts.eq_dec k l)).
Proof.
  induction l.
    intros _ kin.
    inversion kin.

    intros nodup kin.
    inversion kin as [x y kaeq|x y kinl]; subst x y.
      simpl.
      f_equal.
      destruct (KeyFacts.eq_dec k a).
        apply length_remove_1.
        inversion nodup.
        subst.
        intro knotinl.
        apply (InA_eq (l:=l) kaeq) in knotinl.
        contradiction.

        destruct n.
        assumption.

      inversion nodup.
      subst.
      simpl.
      destruct (KeyFacts.eq_dec k a).
        apply (InA_eq (l:=l) e) in kinl.
        contradiction.
        
        f_equal.
        simpl.
        apply IHl; assumption.
Qed.

Lemma nodup_remove (l:list M.key) (k:M.key) : NoDupA M.E.eq l -> NoDupA M.E.eq (removeA KeyFacts.eq_dec k l).
Proof.
  intros.
  induction l.
    simpl.
    assumption.
    
    simpl.
    destruct (KeyFacts.eq_dec k a).
      apply IHl.
      inversion H.
      subst.
      assumption.

      inversion H.
      subst.
      apply NoDupA_cons.
        apply notinA_remove.
        assumption.

        apply IHl.
        assumption.
Qed.

Lemma incl_length (l:list M.key) : forall l':list M.key, NoDupA M.E.eq l' -> inclA M.E.eq l' l -> length l' <= length l.
Proof.
  induction l; intros l' nodup inc.
    apply inclA_nil in inc. 2: apply KeyFacts.eq_equiv.
    subst l'.
    simpl.
    apply Le.le_O_n.

    destruct (InA_dec KeyFacts.eq_dec a l').
      rewrite (length_remove nodup i) in *.
      simpl.
      apply Le.le_n_S.
      apply IHl.
        apply nodup_remove.
        assumption.

        apply (inclA_discard KeyFacts.eq_dec KeyFacts.eq_equiv).
        assumption.

    simpl.
    apply Le.le_trans with (m:=length l); [|apply Le.le_n_Sn].
    apply IHl.
      assumption.

      apply inclA_cons_1 with (a:=a); auto.
      apply KeyFacts.eq_equiv.
Qed.

Lemma incl_length1 (l:list M.key) : forall l':list M.key, forall k:M.key, InA M.E.eq k l -> ~ InA M.E.eq k l' -> NoDupA M.E.eq l' -> inclA M.E.eq l' l -> length l' < length l.
Proof.
  induction l;
  intros l' k kinl knotinl' nodup incl.
    inversion kinl.

    inversion kinl; subst.
      simpl.
      apply Lt.le_lt_n_Sm.
      apply inclA_cons_1 in incl; eauto using KeyFacts.eq_equiv.
        apply incl_length; assumption.

        intro badeq.
        apply M.E.eq_sym in H0.
        apply (InA_eq (l:=l') H0) in badeq.
        contradiction.

      simpl.
      apply Lt.le_lt_trans with (m:=S (length (removeA KeyFacts.eq_dec a l'))).
        destruct (InA_dec KeyFacts.eq_dec a l').
          rewrite <- length_remove.
            apply Le.le_refl.

            assumption.

            assumption.

          rewrite <- length_remove_1.
            apply Le.le_n_Sn.
            assumption.

        apply Lt.lt_n_S.
        apply IHl with (k:=k).
          assumption.

          apply notinA_remove.
          assumption.

          apply nodup_remove.
          assumption.

          apply inclA_discard with (a:=a); eauto using KeyFacts.eq_equiv.
Qed.

Lemma minus_lt : forall m n:nat, n < m -> m - S n < m - n.
Proof.
  clear.
  intros.
  omega.
Qed.


(* The fixed point itself. *)

(* Now we need the map, the dependent type of the result and the step function. *)
Variable m : M.t elt.
Variable T : M.key -> Type.
Variable err_cycle : forall k:M.key, T k.
Variable err_notfound : forall k:M.key, T k.
Variable f:(forall k:M.key, T k) -> forall k:M.key, {e:elt | M.find k m = Some e} -> T k.

(* There's something odd going on with Program here.  I think it's a little
   broken when the recursive call returns a function, so use the explicit
   version to work around it. *)

Program Fixpoint fix_aux (l:list M.key | inclA M.E.eq l (keys m) /\ NoDupA M.E.eq l) {measure (eltsleft m l)}
 : forall k:M.key, T k := fun k =>
  match InA_dec KeyFacts.eq_dec k l with
    | left _ => err_cycle k
    | right _ =>
      let l' := k::l in
        match M.find k m with
          | None => err_notfound k
          | Some v => f (@fix_aux l' _) v
        end
  end.
Next Obligation.
split.
  (* The incl invariant *)
  intros x inkl.
  inversion inkl as [y z xeq|y z xin]; subst y z.
    apply sym_eq in Heq_anonymous.
    apply M.find_2 in Heq_anonymous.
    apply M.elements_1 in Heq_anonymous.
    unfold keys.
    destruct (proj1 (InA_alt (M.eq_key_elt (elt:=elt)) (k,v) (M.elements m)) Heq_anonymous) as [[k'' v''] [[keq'' veq''] in'']].
    simpl in keq'', veq''.
    subst v''.
    apply (M.E.eq_trans (z:=k'') xeq) in keq''.
    eapply InA_eq.
      apply M.E.eq_sym.
      apply keq''.
    apply In_InA.
      apply KeyFacts.eq_equiv.
    apply (proj2 (in_map_iff (fst (A:=M.key) (B:=elt)) (M.elements m) k'')).
    exists (k'',v).
    split.
      reflexivity.

      assumption.

    apply i.
    assumption.

  (* The nodup invariant *)
  apply NoDupA_cons.
    clear - wildcard'.
    induction l.
      auto.

      assumption.

    apply n.
Qed.
Next Obligation.
  (* Termination via reducing measure. *)
  unfold eltsleft.
  simpl.
  apply minus_lt.
  apply incl_length1 with (k:=k).
    apply sym_eq in Heq_anonymous.
    apply M.find_2 in Heq_anonymous.
    apply M.elements_1 in Heq_anonymous.
    destruct (proj1 (InA_alt (M.eq_key_elt (elt:=elt)) (k,v) (M.elements m)) Heq_anonymous) as [[k'' v''] [eq xvin]].
    destruct eq as [keq veq].
    simpl in *.
    subst v''.
    unfold keys.
    eapply InA_eq.
      apply M.E.eq_sym.
      apply keq.
    eapply In_InA.
      apply KeyFacts.eq_equiv.
    apply (proj2 (in_map_iff (fst (A:=M.key) (B:=elt)) (M.elements m) k'')).
    exists (k'',v).
    split.
      reflexivity.

      assumption.

    assumption.

    assumption.

    assumption.
Qed.

Program Definition cfix (k:M.key) : T k := fix_aux nil k.
Next Obligation.
  split.
    intros k' k'in.
    inversion k'in.

    apply NoDupA_nil.
Qed.

End Recursion.

End ChainRecurse.

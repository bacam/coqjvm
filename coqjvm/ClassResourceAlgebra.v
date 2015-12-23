Require Import BasicMachineTypes.
Require Import ResourceAlgebra.
Require FMapAVL.
Require FMapInterface.
Require FMapFacts.
Require Sorting.
Require SetoidList.
Require Import Peano_dec.
Require Import Bool_nat.
Require Import OrderedType.
Require Import FMapCombine.

Module Type FILTER (B : BASICS).
Parameter f : B.Classname.t -> bool.
End FILTER.

Module ClassResourceAlgebra (B : BASICS)
                            (F : FILTER B)
  <: RESOURCE_ALGEBRA B.

Module RA_F := F.

Inductive count : Set :=
| Fin : nat -> count
| Inf : count.

Inductive count_leq : count -> count -> Prop :=
| count_leq_inf : forall c : count, count_leq c Inf
| count_leq_fin : forall (n1 n2 : nat), n1 <= n2 -> count_leq (Fin n1) (Fin n2).

Lemma count_leq_refl : forall (c : count), count_leq c c.
Proof.
  destruct c.
  apply count_leq_fin.  apply Le.le_refl.
  apply count_leq_inf.
Qed.

Lemma count_leq_antisymm : forall (c c' : count),
  count_leq c c' -> count_leq c' c -> c = c'.
Proof.
  intros.
  destruct c; destruct c'.
  inversion H. inversion H0. subst.
  apply (Le.le_antisym n n0 H3) in H6.
  rewrite H6.
  reflexivity.

  inversion H0.

  inversion H.

  reflexivity.
Qed.

Lemma count_leq_trans : forall (c1 c2 c3 : count),
  count_leq c1 c2 -> count_leq c2 c3 -> count_leq c1 c3.
Proof.
  intros c1 c2 c3 leq1 leq2.
  inversion leq1; inversion leq2; subst.
    apply count_leq_inf.

    discriminate.

    apply count_leq_inf.

    apply count_leq_fin.
    apply Le.le_trans with (m:= n2). assumption.
    injection H3. intro neq.  rewrite <- neq.
    assumption.
Qed.

Lemma count_leq_zero : forall c : count, count_leq (Fin 0) c.
Proof.
  destruct c.
    apply count_leq_fin.
    apply Le.le_O_n.

    apply count_leq_inf.
Qed.


Definition count_sum (c1 c2 : count) : count :=
  match c1 with
    | Inf => Inf
    | Fin n => match c2 with | Inf => Inf | Fin n' => Fin (n+n') end
  end.

Lemma count_sum_lzero : forall c : count, count_sum (Fin 0) c = c.
Proof.
  intro c.
  induction c.
    simpl.
    auto.

    reflexivity.
Qed.

Lemma count_sum_rzero : forall c : count, count_sum c (Fin 0) = c.
Proof.
  intro c.
  induction c.
    simpl.
    auto.

    reflexivity.
Qed.

Lemma count_sum_leq : forall c1 c2 c1' c2',
  count_leq c1 c2 -> count_leq c1' c2' ->
  count_leq (count_sum c1 c1') (count_sum c2 c2').
Proof.
  intros c1 c2 c1' c2' leq leq'.
  inversion leq;
  inversion leq';
  subst; simpl; try constructor.
    apply Plus.plus_le_compat; assumption.
Qed.


Module Res := FMapAVL.Make B.Classname.
Module ResFacts := FMapFacts.Facts Res.
Module ResCombine := FMapCombine.FMapCombine Res.
Definition res := Res.t count.

Definition mapsto (k : Res.key) (c : count) (r : res) :=
  Res.MapsTo k c r \/ (~ Res.In k r /\ c = Fin 0).

Lemma mapsto_maymapto (k : Res.key) (c : count) (r : res) :
  mapsto k c r <-> (exists c', ResCombine.maymapto count k c' r /\ (c' = Some c \/ (c' = None /\ c = Fin 0))).
Proof.
  intros.
  split.
    intros maps.
    destruct maps as [maps|[notin iszero]].
      exists (Some c).
      unfold ResCombine.maymapto.
      split; [right;exists c|]; auto.

      exists (None (A:=count)).
      unfold ResCombine.maymapto.
      auto.

    intros [c' [maps val]].
    destruct val as [some|[none zero]].
      rewrite some in maps.
      inversion maps as [[silly _]|[c'' [c''eq maps']]].
        discriminate.

        injection c''eq as c''eq'.
        rewrite <- c''eq' in *.
        left.
        apply maps'.
        
      right.
      split; [|apply zero].
      inversion maps as [[none' notin]|[c'' [silly _]]].
        apply notin.

        rewrite silly in *.
        discriminate.
Qed.

Lemma mapsto_eq (k : Res.key) (r : res) :
  forall c1:count, mapsto k c1 r -> forall c2:count, mapsto k c2 r -> c1 = c2.
Proof.
  intros c1 maps1 c2 maps2.
  unfold mapsto in *.
  destruct maps1; destruct maps2.
    apply Res.find_1 in H.
    apply Res.find_1 in H0.
    rewrite H0 in H.
    injection H.
    auto.

    destruct H0.
    unfold Res.In in H0.
    assert (exists e : count, Res.MapsTo k e r).
    exists c1. assumption. contradiction.

    destruct H.
    unfold Res.In in H.
    assert (exists e : count, Res.MapsTo k e r).
    exists c2. assumption. contradiction.

   destruct H as [_ c1e].  destruct H0 as [_ c2e].
   rewrite c1e.  rewrite c2e.
   reflexivity.
Qed.

(* Anything not mentioned in the map is zero. *)
Lemma mapsto_always (k : Res.key) (r : res) :
  exists c:count, mapsto k c r.
Proof.
  intros.
  case_eq (Res.find k r).
    intros c H.
    exists c.
    unfold mapsto.
    left. apply Res.find_2. assumption.

    intro H.
    exists (Fin 0).
    unfold mapsto.
    right. split.
      apply (proj2 (ResFacts.not_find_mapsto_iff r k)).
      assumption.

      reflexivity.
Qed.

Implicit Arguments mapsto_eq [k c1 c2 r].

Definition eq := fun (m1 m2 : res) => forall (k : Res.key),
  forall c : count, mapsto k c m1  <-> mapsto k c m2.

Notation "e1 [=] e2" := (eq e1 e2) (at level 70, no associativity).

Lemma eq_refl : forall r, r [=] r.
Proof.
  unfold eq.
  split; intro H; assumption.
Qed.

Lemma eq_symm : forall r1 r2, r1 [=] r2 -> r2 [=] r1.
Proof.
  intros r1 r2 H.
  unfold eq in *.
  intros.
  apply iff_sym.
  apply H.
Qed.

Lemma eq_trans : forall r1 r2 r3, r1 [=] r2 -> r2 [=] r3 -> r1 [=] r3.
Proof.
  intros r1 r2 r3 eq1 eq2.
  unfold eq in *.
  intros.
  apply iff_trans with (B := mapsto k c r2); auto.
Qed.

Add Relation res eq
 reflexivity proved by eq_refl
 symmetry proved by eq_symm
 transitivity proved by eq_trans as ra_eq_rel.


Definition leq (r1 r2 : res) : Prop :=
  forall (k : Res.key) (c1 c2 : count),
    mapsto k c1 r1 /\ mapsto k c2 r2 -> count_leq c1 c2.

Notation "e1 <: e2" := (leq e1 e2) (at level 75, no associativity).

Lemma leq_refl: forall r1 r2, r1 [=] r2 -> r1 <: r2.
Proof.
  unfold leq, eq.
  intros r1 r2 req k c1 c2 maps.
  destruct maps as [maps1 maps2].
  destruct (req k c1) as [maps1' _].
  apply maps1' in maps1.
  apply (mapsto_eq maps1) with (c2 := c2) in maps2.
  rewrite maps2.
  apply count_leq_refl.
Qed.

Lemma leq_antisymm: forall r1 r2, r1 <: r2 -> r2 <: r1 -> r1 [=] r2.
Proof.
  intros r1 r2 leq1 leq2.
  unfold eq.
  intros k c.
  split; intro H.
    unfold leq in *.
    assert (maps2 : exists c', mapsto k c' r2).
    apply mapsto_always.
    destruct maps2 as [c' maps2].
    assert (leq1': count_leq c c').
      apply leq1 with (k:=k) (c1:=c) (c2:=c').
      split; assumption.

    assert (leq2': count_leq c' c).
      apply leq2 with (k:=k) (c1:=c') (c2:=c).
      split; assumption.

    apply (count_leq_antisymm c c' leq1') in leq2'.
    rewrite leq2'.
    assumption.


    unfold leq in *.
    assert (maps1 : exists c', mapsto k c' r1).
    apply mapsto_always.
    destruct maps1 as [c' maps1].
    assert (leq1': count_leq c' c).
      apply leq1 with (k:=k) (c1:=c') (c2:=c).
      split; assumption.

    assert (leq2': count_leq c c').
      apply leq2 with (k:=k) (c1:=c) (c2:=c').
      split; assumption.

    apply (count_leq_antisymm c' c leq1') in leq2'.
    rewrite <- leq2'.
    assumption.
Qed.

Lemma leq_trans : forall r1 r2 r3, r1 <: r2 -> r2 <: r3 -> r1 <: r3.
Proof.
  unfold leq.
  intros r1 r2 r3 leq1 leq2 k c1 c3 maps.
  destruct maps as [maps1 maps3].
  assert (maps2 : exists c2, mapsto k c2 r2).
    apply mapsto_always.
  destruct maps2 as [c2 maps2].
  apply count_leq_trans with (c2:=c2).
    apply leq1 with (k:=k).
    split; assumption.

    apply leq2 with (k:=k).
    split; assumption.
Qed.

Definition leq_refl2 : forall x, x <: x := fun x => leq_refl x x (eq_refl x).

Add Relation res leq
 reflexivity proved by leq_refl2
 transitivity proved by leq_trans as ra_leq_rel.

Add Morphism leq with signature eq ==> eq ==> iff as leq_morphism.
intuition eauto 6 using leq_trans, leq_refl, eq_symm.
Qed.


Definition combine := ResCombine.combine count_sum.
Notation "e1 :*: e2" := (combine e1 e2) (at level 40, left associativity).

Lemma maymapto_always (k:Res.key) (r:res) :
  exists c:option count, ResCombine.maymapto count k c r.
Proof.
  intros.
  destruct (mapsto_always k r) as [c cmapsto].
  destruct cmapsto as [cmapsto|[notin zero]].
    exists (Some c).
    right.
    exists c.
    auto.

    exists (None (A:=count)).
    left.
    auto.
Qed.

Lemma combine_maps (k:Res.key) (c1 c2:count) (r1 r2:res) :
  mapsto k c1 r1 -> mapsto k c2 r2 -> mapsto k (count_sum c1 c2) (r1 :*: r2).
Proof.
  intros maps1 maps2.

  apply (proj2 (mapsto_maymapto k (count_sum c1 c2) (r1 :*: r2))).
  destruct (proj1 (mapsto_maymapto k c1 r1) maps1) as [c1' [maps1' val1]].
  destruct (proj1 (mapsto_maymapto k c2 r2) maps2) as [c2' [maps2' val2]].
  exists (ResCombine.option_f count count_sum c1' c2').
  split.
    unfold combine.
    apply ResCombine.combine_1; assumption.

    destruct val1 as [c1some|[c1none c1z]];
    destruct val2 as [c2some|[c2none c2z]];
    try subst c1;
    try subst c2;
    subst c1' c2';
    try rewrite count_sum_lzero;
    try rewrite count_sum_rzero;
    simpl;
    auto.
Qed.
  

Definition extends (r1 r2:res) :=
  forall (k:Res.key) (c:count), mapsto k c r1 -> mapsto k c r2.

(* Half of combine_morphism. *)
Lemma combine_morphism_imp : forall r1 r2 r1' r2',
  r1 [=] r1' ->
  r2 [=] r2' ->
  extends (r1 :*: r2) (r1' :*: r2').
Proof.
  intros r1 r2 r1' r2' r1eq r2eq k c.
  intro maps.
  apply (proj2 (mapsto_maymapto k c (r1' :*: r2'))).
  apply (proj1 (mapsto_maymapto k c (r1 :*: r2))) in maps.
  destruct maps as [c' [maps val]].
  destruct (mapsto_always k r1) as [c1 c1mapsto].
  destruct (mapsto_always k r2) as [c2 c2mapsto].
  set (c1maymapto := (proj1 (mapsto_maymapto k c1 r1)) c1mapsto).
  set (c2maymapto := (proj1 (mapsto_maymapto k c2 r2)) c2mapsto).
  destruct c1maymapto as [c1' [c1maymapto c1val]].
  destruct c2maymapto as [c2' [c2maymapto c2val]].
  set (combmap := ResCombine.combine_1 (f:=count_sum) r1 r2 k c1' c2' c1maymapto c2maymapto).
  set (ceq := ResCombine.maymapto_eq count k c' (ResCombine.option_f count count_sum c1' c2') (r1:*:r2) maps combmap).
  apply (proj1 (r1eq k c1)) in c1mapsto.
  apply (proj1 (r2eq k c2)) in c2mapsto.
  set (c1maymapto' := (proj1 (mapsto_maymapto k c1 r1')) c1mapsto).
  set (c2maymapto' := (proj1 (mapsto_maymapto k c2 r2')) c2mapsto).
  destruct c1maymapto' as [c1'' [c1maymapto' c1val']].
  destruct c2maymapto' as [c2'' [c2maymapto' c2val']].
  set (combmap' := ResCombine.combine_1 (f:=count_sum) r1' r2' k c1'' c2'' c1maymapto' c2maymapto').
  exists (ResCombine.option_f count count_sum c1'' c2'').
  split.
    assumption.

    (* Lots of cases.  May be a little redundant? *)
    destruct val as [c'eq|[c'eq cz]];
    destruct c1val as [c1eq|[c1eq c1z]];
    destruct c2val as [c2eq|[c2eq c2z]];
    (destruct c1val' as [c1''eq|[c1''eq c1eq']];[|rewrite c1eq' in *]);
    (destruct c2val' as [c2''eq|[c2''eq c2eq']];[|rewrite c2eq' in *]);
    subst c' c1' c1'' c2' c2'';
    cbv beta delta [ResCombine.option_f] iota zeta in *;
    try injection ceq as ceq0;
    try subst c1 c2;
    try subst c;
    try rewrite count_sum_lzero in *;
    try rewrite count_sum_rzero in *;
    simpl in *;
    auto; try discriminate.
    (* FIXME: this didn't used to be necessary *)
    destruct c2; auto.
Qed.

Add Morphism combine with signature  eq ==>  eq ==>  eq as combine_morphism.
  intros r1 r2 eq1 r1' r2' eq2.
  split.
    apply combine_morphism_imp; assumption.

    apply combine_morphism_imp; auto using eq_symm.
Qed.

Definition e : res := Res.empty count.

Lemma e_bottom : forall r, e <: r.
Proof.
  intros r k c1 c2 [maps1 maps2].
  destruct maps1 as [maps1|[notin zero]].
    destruct (Res.empty_1 maps1).

    rewrite zero.
    apply count_leq_zero.
Qed.

Lemma e_zero_1 : forall k, mapsto k (Fin 0) e.
Proof.
  intro k.
  right.
  split.
    intros [c ine].
    apply (Res.empty_1 ine).

    reflexivity.
Qed.

Lemma e_zero_2 : forall k, ResCombine.maymapto count k None e.
Proof.
  intro k.
  unfold ResCombine.maymapto.
  left.
  split.
    reflexivity.

    intros [c ine].
    apply (Res.empty_1 ine).
Qed.

Lemma e_combine_r : forall r, e :*: r [=] r.
Proof.
  intros r k c.
  split.
    intro maps1.
    rewrite mapsto_maymapto in *.
    destruct maps1 as [c' [maymap val]].
    exists c'.
    unfold combine in maymap.
    destruct (mapsto_always k r) as [rc rcmaps].
    destruct (proj1 (mapsto_maymapto k rc r) rcmaps) as [rc' [rcmaymapto rcval]].
    set (combmap := ResCombine.combine_1 (f:=count_sum) e r k None rc' (e_zero_2 k) rcmaymapto).
    simpl in combmap.
    set (ceq := ResCombine.maymapto_eq count k c' rc' (ResCombine.combine count_sum e r) maymap combmap).
    rewrite ceq in *.
    auto.

    intro maps1.
    rewrite mapsto_maymapto in *.
    destruct maps1 as [c' [maymap val]].
    exists c'.
    split; [|assumption].
    set (combmap := ResCombine.combine_1 (f:=count_sum) e r k None c' (e_zero_2 k) maymap).
    simpl in combmap.
    assumption.
Qed.

Lemma combine_symm_half : forall r1 r2, extends (r1 :*: r2) (r2 :*: r1).
Proof.
  intros r1 r2 k c maps.
  rewrite mapsto_maymapto in *.
  destruct maps as [c' [maymap val]].
  exists c'.
  split; [clear c val|assumption].
  destruct (mapsto_always k r1) as [c1 c1maps].
  destruct (proj1 (mapsto_maymapto k c1 r1) c1maps) as [c1' [c1maymapto c1val]].
  destruct (mapsto_always k r2) as [c2 c2maps].
  destruct (proj1 (mapsto_maymapto k c2 r2) c2maps) as [c2' [c2maymapto c2val]].
  set (combmap := ResCombine.combine_1 (f:=count_sum) r1 r2 k c1' c2' c1maymapto c2maymapto).
  set (ceq := ResCombine.maymapto_eq count k c' (ResCombine.option_f count count_sum c1' c2') (ResCombine.combine count_sum r1 r2) maymap combmap).
  set (combmap' := ResCombine.combine_1 (f:=count_sum) r2 r1 k c2' c1' c2maymapto c1maymapto).
  rewrite ResCombine.option_f_sym in combmap'.
    rewrite <- ceq in combmap'.
    assumption.

    (* count_sum is symmetric. *)
    clear.
    intros.
    destruct e1'; destruct e2'; simpl; auto with arith.
Qed.

Lemma combine_symm : forall r1 r2, r1 :*: r2 [=] r2 :*: r1.
  split; apply combine_symm_half.
Qed.

Lemma r_combine_e : forall r, r :*: e [=] r.
Proof.
  intro.
  apply eq_trans with (r2:=e :*: r).
    apply combine_symm.

    apply e_combine_r.
Qed.

Lemma combine_assoc : forall r1 r2 r3, r1 :*: (r2 :*: r3) [=] (r1 :*: r2) :*: r3.
Proof.
  intros.
  split; intro maps;
  rewrite mapsto_maymapto in *;
  destruct maps as [c' [maymap val]];
  exists c';
  destruct (mapsto_always k r1) as [c1 c1maps];
  destruct (proj1 (mapsto_maymapto k c1 r1) c1maps) as [c1' [c1maymapto c1val]];
  destruct (mapsto_always k r2) as [c2 c2maps];
  destruct (proj1 (mapsto_maymapto k c2 r2) c2maps) as [c2' [c2maymapto c2val]];
  destruct (mapsto_always k r3) as [c3 c3maps];
  destruct (proj1 (mapsto_maymapto k c3 r3) c3maps) as [c3' [c3maymapto c3val]];
  set (combmap12 := ResCombine.combine_1 (f:=count_sum) r1 r2 k c1' c2' c1maymapto c2maymapto);
  set (combmap23 := ResCombine.combine_1 (f:=count_sum) r2 r3 k c2' c3' c2maymapto c3maymapto);
  set (combmap12_3 := ResCombine.combine_1 (f:=count_sum) (r1:*:r2) r3 k (ResCombine.option_f count count_sum c1' c2') c3' combmap12 c3maymapto);
  set (combmap1_23 := ResCombine.combine_1 (f:=count_sum) r1 (r2:*:r3) k c1' (ResCombine.option_f count count_sum c2' c3') c1maymapto combmap23);
  assert (opt_f_trans :
    (ResCombine.option_f count count_sum c1' (ResCombine.option_f count count_sum c2' c3')) =
    (ResCombine.option_f count count_sum (ResCombine.option_f count count_sum c1' c2') c3')) by
    (clear;
      (destruct c1'; destruct c2'; destruct c3'; auto);
      simpl;
      f_equal;
      destruct c; destruct c0; destruct c1; unfold count_sum; auto with arith).

    set (ceq := ResCombine.maymapto_eq count k c'
      (ResCombine.option_f count count_sum c1' (ResCombine.option_f count count_sum c2' c3'))
      (r1 :*: (r2 :*: r3)) maymap combmap1_23).
    rewrite opt_f_trans in ceq.
    rewrite <- ceq in combmap12_3.
    auto.

    set (ceq := ResCombine.maymapto_eq count k c'
      (ResCombine.option_f count count_sum (ResCombine.option_f count count_sum c1' c2') c3')
      ((r1 :*: r2) :*: r3) maymap combmap12_3).
    rewrite <- opt_f_trans in ceq.
    rewrite <- ceq in combmap1_23.
    auto.
Qed.

Lemma combine_form_eq : forall k c c1 c2 r1 r2,
  mapsto k c1 r1 -> mapsto k c2 r2 -> mapsto k c (r1 :*: r2) -> c = count_sum c1 c2.
Proof.
  intros k c c1 c2 r1 r2 maps1 maps2 maps.
  rewrite mapsto_maymapto in *.
  destruct maps1 as [c1m [maymap1 val1]].
  destruct maps2 as [c2m [maymap2 val2]].
  destruct maps as [cm [maymap val]].
  pose (combmap12 := ResCombine.combine_1 (f:=count_sum) r1 r2 k c1m c2m maymap1 maymap2).
  pose (ceq := ResCombine.maymapto_eq count k cm (ResCombine.option_f count count_sum c1m c2m) (ResCombine.combine count_sum r1 r2) maymap combmap12).
  rewrite ceq in *.
  destruct val1 as [c1eq|[c1eq c1z]];
  destruct val2 as [c2eq|[c2eq c2z]];
  destruct val  as [cveq|[cveq cvz]];
  subst c1m c2m;
  try subst c1;
  try subst c2;
  try rewrite count_sum_lzero in *;
  try rewrite count_sum_rzero in *;
  simpl in *; first [injection cveq;auto | discriminate | assumption].
Qed.

Add Morphism combine with signature leq ++> leq ++> leq as combine_order.
  intros r1 r1' r1le r2 r2' r2le k c c' [maps maps'].
  destruct (mapsto_always k r1) as [c1 c1maps].
  destruct (mapsto_always k r2) as [c2 c2maps].
  pose (ceq := combine_form_eq k c c1 c2 r1 r2 c1maps c2maps maps).
  destruct (mapsto_always k r1') as [c1' c1maps'].
  destruct (mapsto_always k r2') as [c2' c2maps'].
  pose (ceq' := combine_form_eq k c' c1' c2' r1' r2' c1maps' c2maps' maps').
  pose (le1 := r1le k c1 c1' (conj c1maps c1maps')).
  pose (le2 := r2le k c2 c2' (conj c2maps c2maps')).
  rewrite ceq. rewrite ceq'.
  apply count_sum_leq; assumption.
Qed.

Definition bang_sum := 
  fun c => match c with
             | Fin 0 => Fin 0
             | _ => Inf
           end.
Definition bang : res -> res := Res.map bang_sum.

Notation "! e" := (bang e) (at level 35, right associativity).

Lemma bang_inv : forall k c r,
  mapsto k c (!r) -> c = Fin 0 \/ c = Inf.
Proof.
  intros k c r maps.
  unfold bang in maps.
  destruct maps as [maps|[_ zero]].
    destruct (proj1 (ResFacts.map_mapsto_iff r k c bang_sum) maps)
      as [c0 [ceq maps0]].
    destruct c0; [destruct n|]; simpl; auto.

    auto.
Qed.

Lemma bang_apply : forall k c r,
  mapsto k c r -> mapsto k (bang_sum c) (!r).
Proof.
  intros k c r maps.
  destruct maps as [maps|[notin zero]].
    apply Res.map_1 with (f:=bang_sum) in maps.
    left.
    assumption.

    right.
    split.
      intro inbangr.
      apply (proj1 (ResFacts.map_in_iff r k bang_sum)) in inbangr.
      contradiction.

      subst c.
      reflexivity.
Qed.

Lemma bang_unit : forall r, r <: !r.
Proof.
  intros r k c1 c2 [maps1 maps2].
  destruct (bang_inv k c2 r maps2); subst c2.
    apply bang_apply in maps1.
    apply (mapsto_eq maps1) in maps2.
    destruct c1 as [[|n]|].
      apply count_leq_fin.
      auto.

      simpl in *.
      discriminate.

      simpl in *.
      discriminate.

    apply count_leq_inf.
Qed.

Lemma bang_mult : forall r, !!r <: !r.
Proof.
  intros r k c1 c2 [maps1 maps2].
  destruct (bang_inv _ _ _ maps2) as [c2eq|c2eq];
  apply bang_apply in maps2;
  subst c2;
  set (ceq := mapsto_eq maps1 maps2);
  rewrite ceq;
  simpl.
    apply count_leq_fin.
    apply Le.le_O_n.

    apply count_leq_inf.
Qed.

Lemma bang_codup : forall r, !r :*: !r <: !r.
Proof.
  intros r k c1 c2 [maps1 maps2].

  set (maps2' := combine_maps k c2 c2 (!r) (!r) maps2 maps2).
  set (ceq := mapsto_eq maps1 maps2').
  destruct (bang_inv _ _ _ maps2) as [c2z|c2i];
  subst c2;
  rewrite ceq;
  simpl.
    apply count_leq_fin.
    apply Le.le_O_n.

    apply count_leq_inf.
Qed.

Lemma bang_e : !e [=] e.
Proof.
  intros k c.
  assert (mapsz : mapsto k (Fin 0) e) by apply e_zero_1.
  split; intro maps.
    apply bang_apply in mapsz.
    simpl in mapsz.
    rewrite (mapsto_eq maps mapsz).
    apply e_zero_1.

    rewrite (mapsto_eq maps mapsz).
    apply bang_apply in mapsz.
    simpl in mapsz.
    assumption.
Qed.

Lemma bang_combine : forall r1 r2, !(r1 :*: r2) [=] !r1 :*: !r2.
Proof.
  intros r1 r2 k c.
  destruct (mapsto_always k r1) as [c1 c1maps].
  destruct (mapsto_always k r2) as [c2 c2maps].
  set (maps1 := bang_apply _ _ _ (combine_maps _ _ _ _ _ c1maps c2maps)).
  set (maps2 := combine_maps _ _ _ _ _ (bang_apply _ _ _ c1maps) (bang_apply _ _ _ c2maps)).
  assert (commutes : bang_sum (count_sum c1 c2) = count_sum (bang_sum c1) (bang_sum c2)).
    destruct c1 as [[|n1]|]; destruct c2 as [[|n2]|]; try reflexivity.

  split; intro maps.
    rewrite (mapsto_eq maps maps1).
    rewrite commutes.
    assumption.

    rewrite (mapsto_eq maps maps2).
    rewrite <- commutes.
    assumption.
Qed.

Add Morphism bang with signature leq ++> leq as bang_order.
Proof.
  intros r1 r2 rle k c1 c2 [maps1 maps2].

  destruct (mapsto_always k r1) as [c1' maps1'].
  destruct (mapsto_always k r2) as [c2' maps2'].
  pose (maps1'' := bang_apply _ _ _ maps1').
  pose (maps2'' := bang_apply _ _ _ maps2').
  apply (mapsto_eq maps1) in maps1''.
  apply (mapsto_eq maps2) in maps2''.
  subst c1 c2.
  pose (cle:=rle k c1' c2' (conj maps1' maps2')).
  destruct c1' as [[|n1]|]; destruct c2' as [[|n2]|];
    try apply count_leq_zero;
    simpl; auto using count_leq_inf.

    inversion cle.
    pose (Le.le_Sn_O n1).
    contradiction.
Qed.

Add Morphism bang with signature  eq ==>  eq as bang_morphism.
Proof.
  intros r1 r2 req k c.
  split; intro maps.
    destruct (mapsto_always k r1) as [c1 maps1].
    assert (c = bang_sum c1).
      apply mapsto_eq with (k:=k) (r:= !r1); [assumption|].
      apply bang_apply.
      assumption.
    subst c.
    apply bang_apply.
    pose (maps2 := proj1 (req _ _) maps1).
    assumption.

    destruct (mapsto_always k r2) as [c2 maps2].
    assert (c = bang_sum c2).
      apply mapsto_eq with (k:=k) (r:= !r2); [assumption|].
      apply bang_apply.
      assumption.

    subst c.
    apply bang_apply.
    pose (maps1 := proj2 (req _ _) maps2).
    assumption.
Qed.

Definition r_new : B.Classname.t -> option res :=
  fun c => if F.f c then Some (Res.add c (Fin 1) (Res.empty count)) else None.

Fixpoint res_parse (expr:res_expr B.Classname.t) :=
  match expr with
    | List.nil => e
    | (List.cons (true,c) t) => match r_new c with None => res_parse t | Some r => (!r) :*: (res_parse t) end
    | (List.cons (false,c) t) => match r_new c with None => res_parse t | Some r => r :*: (res_parse t) end
  end.

End ClassResourceAlgebra.


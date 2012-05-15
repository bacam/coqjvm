Require FMapInterface.
Require FMapFacts.
Require Import OrderedType.

Module FMapCombine (M : FMapInterface.S).

Module KeyFacts := OrderedTypeFacts M.E.
Module MapFacts := FMapFacts.Facts M.

Section Combine.

Variable elt : Set.
Variable f : elt -> elt -> elt.

Let combine_aux :=
  (fun k e r =>
    let e'' :=
      match M.find k r with
        | Some e' => f e e'
        | None => e
      end
      in M.add k e'' r).

Definition combine (r1 r2 : M.t elt) : M.t elt :=
  M.fold combine_aux r1 r2.

Lemma sorted_head_lowest : forall (x y:M.key*elt) (l:List.list (M.key*elt)),
  Sorting.sort (M.lt_key (elt:=elt)) (List.cons y l) ->
  SetoidList.InA (M.eq_key_elt (elt:=elt)) x l ->
  M.lt_key y x.
Proof.
  clear.
  induction l; intros sorted intail.
    inversion intail.

    destruct x as [kx ex].
    destruct y as [ky ey].
    destruct a as [ka ea].
    inversion intail as [p q eq|p q intail']; subst.
      apply Sorting.sort_inv in sorted.
      apply proj2 in sorted.
      apply Sorting.lelistA_inv in sorted.
      unfold M.lt_key in *.
      unfold M.eq_key_elt in *.
      simpl in *.
      apply proj1 in eq.
      apply M.E.eq_sym in eq.
      apply KeyFacts.lt_eq with (y:=ka); assumption.

      apply IHl.
        apply Sorting.sort_inv in sorted.
        destruct sorted as [sorted1 le1].
        apply Sorting.lelistA_inv in le1.
        apply Sorting.sort_inv in sorted1.
         destruct sorted1 as [sorted2 le2].
        inversion le2 as [|[k e] t].
          apply Sorting.cons_sort.
            apply Sorting.nil_sort.
        
            apply Sorting.nil_leA.

          subst.
          apply Sorting.cons_sort.
            assumption.

            apply Sorting.cons_leA.
            unfold M.lt_key.
            simpl.
            apply M.E.lt_trans with (y:=ka); assumption.

        assumption.
Qed.

(* Some extra definitions to help reason about keys that aren't in one of the
   maps. *)
Definition option_f (e1 e2 : option elt) : option elt :=
  match e1 with
    | None => e2
    | Some e1' =>
      Some match e2 with
             | None => e1'
             | Some e2' => f e1' e2'
           end
  end.

Lemma option_f_sym : forall (e1 e2 : option elt),
  (forall (e1' e2' : elt), f e1' e2' = f e2' e1') ->
  option_f e1 e2 = option_f e2 e1.
Proof.
  intros e1 e2 fsym.
  destruct e1; destruct e2; simpl; [rewrite fsym| | | ]; auto.
Qed.
  

Definition maymapto (k : M.key) (e : option elt) (m : M.t elt) : Prop :=
  (e = None /\ ~ M.In k m) \/ (exists e', e = Some e' /\ M.MapsTo k e' m).

Lemma maymapto_list : forall (k : M.key) (e : option elt) (m : M.t elt),
  maymapto k e m ->
  (e = None /\ ~ (exists e', SetoidList.InA (M.eq_key_elt (elt:=elt)) (k,e') (M.elements m))) \/
  (exists e', e = Some e' /\ SetoidList.InA (M.eq_key_elt (elt:=elt)) (k,e') (M.elements m)).
Proof.
  intros k e m maps.
  destruct maps as [maps|maps].
    destruct maps as [enone notin].
    left.
    split. assumption.
    intro kinm.
    destruct kinm as [e' kinm].
    apply M.elements_2 in kinm.
    apply (ex_intro (fun e' => M.MapsTo k e' m)) in kinm.
    contradiction.

    right.
    destruct maps as [e' [eeq maps]].
    exists e'.
    split. assumption.
    apply M.elements_1.
    assumption.
Qed.

Lemma maymapto_1 : forall (x y : M.key) (e : option elt) (m : M.t elt),
  M.E.eq x y -> maymapto x e m -> maymapto y e m.
Proof.
  intros x y e m xyeq xmap.
  destruct xmap as [[enone xnotin]|[e' [eeq ein]]].
    left.
    split; [assumption|].
    intro yin.
    apply MapFacts.In_iff with (elt:=elt) (m:=m) in xyeq.
    apply (proj2 xyeq) in yin.
    contradiction.

    right.
    exists e'.
    split; [assumption|].
    apply M.MapsTo_1 with (x:=x); assumption.
Qed.

Lemma maymapto_find : forall (x : M.key) (e : option elt) (m : M.t elt),
  maymapto x e m -> M.find x m = e.
Proof.
  intros x e m maps.
  destruct maps as [[enone enotin]|[e' [eeq ein]]].
    rewrite enone.
    apply (proj1 (MapFacts.not_find_mapsto_iff m x)).
    assumption.

    rewrite eeq.
    apply (proj1 (MapFacts.find_mapsto_iff m x e')).
    assumption.
Qed.

Lemma maymapto_add_1 : forall (x : M.key) (e : elt) (m : M.t elt),
  maymapto x (Some e) (M.add x e m).
Proof.
  intros.
  right.
  exists e.
  split; [reflexivity|].
  apply M.add_1.
  apply M.E.eq_refl.
Qed.

Lemma maymapto_add_2 : forall (x y : M.key) (e : option elt) (e': elt) (m : M.t elt),
  ~ M.E.eq x y -> maymapto x e m -> maymapto x e (M.add y e' m).
Proof.
  intros x y e e' m neq xmap.
  destruct xmap as [[enone enotin]|[ev [eeq ein]]].
    left.
    split; [assumption|].
    set (neq' := (fun eq => neq (M.E.eq_sym eq))).
    intro xin.
    apply (proj1 (MapFacts.add_neq_in_iff m e' neq')) in xin.
    contradiction.

    right.
    exists ev.
    split; [assumption|].
    apply M.add_2; auto.
Qed.

Lemma maymapto_eq : forall (k : M.key) (e e' : option elt) (m : M.t elt),
  maymapto k e m -> maymapto k e' m -> e = e'.
Proof.
  intros k e e' m emap e'map.
  destruct emap as [[enone enotin]|[ev [eveq evin]]];
  destruct e'map as [[e'none e'notin]|[e'v [e'veq e'vin]]];
  subst; auto.
    apply (ex_intro (fun e => M.MapsTo k e m)) in e'vin.
    contradiction.

    apply (ex_intro (fun e => M.MapsTo k e m)) in evin.
    contradiction.

    f_equal.
    apply MapFacts.MapsTo_fun with (x:=k) (m:=m); assumption.
Qed.

Theorem combine_1 : forall (m1 m2 : M.t elt) (k:M.key) (e1 e2:option elt),
  maymapto k e1 m1 -> maymapto k e2 m2 -> maymapto k (option_f e1 e2) (combine m1 m2).
Proof.
  intros m1 m2 k e1 e2 maps1 maps2.
  unfold combine.
  rewrite M.fold_1.
  apply maymapto_list in maps1.
  set (lsorted:=M.elements_3 m1).
  set (l:=M.elements m1).
  change (M.elements m1) with l in maps1.
  change (M.elements m1) with l in lsorted.

  generalize l m2 maps1 maps2 lsorted.
  clear      l m2 maps1 maps2 lsorted.
  induction l as [|[k' e] l]; intros m2 maps1 maps2 lsorted.
    inversion maps1 as [[e1none _]|[e1' [_ silly]]].
      unfold option_f.
      rewrite e1none.
      simpl.
      assumption.

      inversion silly.

    inversion maps1 as [[e1none notin]|[e1' [e1some e1in]] (*[[k'' e''] t eq''|[k'' e''] t intail]*)].
      (* The case where k is not in m1 (so e1 = None) *)
      simpl.
      apply IHl.
        left.
        split. assumption.
        intros [e' maybein].
        apply SetoidList.InA_cons_tl with (y:=(k',e)) in maybein.
        apply (ex_intro (fun e' => InA (M.eq_key_elt (elt:=elt)) (k, e') ((k', e) :: l))) in maybein.
        contradiction.

        unfold combine_aux.
        destruct maps2 as [[e2none e2notin]|[e2' [e2eq e2in]]].
          unfold maymapto.
          left.
          split. assumption.
          intro kin.
          apply (proj1 (MapFacts.add_in_iff m2 k' k (match M.find k' m2 with
             | Some e' => f e e'
             | None => e end))) in kin.
          destruct kin; [|contradiction].
          destruct notin.
          exists e.
          apply SetoidList.InA_cons_hd.
          unfold M.eq_key_elt.
          simpl.
          split; [apply M.E.eq_sym;assumption|reflexivity].

          unfold maymapto.
          right.
          exists e2'.
          split. assumption.
          apply M.add_2; [|assumption].
          intro keq.
          destruct notin.
          exists e.
          apply SetoidList.InA_cons_hd.
          unfold M.eq_key_elt.
          split; [apply M.E.eq_sym;assumption|reflexivity].

          apply Sorting.sort_inv in lsorted.
          destruct lsorted as [lsorted _].
          assumption.

      (* The case where k is in m1. *)
      inversion e1in as [[k'' e''] t eq''|[k'' e''] t intail]; subst.
        (* k is first in the list. *)
        clear IHl.
        destruct eq'' as [keq eeq].
        simpl in eeq, keq. 
        rewrite eeq in *. clear eeq.
        apply maymapto_1 with (x:=k) (y:=k') in maps2.
        2:assumption.
        apply M.E.eq_sym in keq.
        apply maymapto_1 with (x:=k'). assumption.
        clear keq.
        simpl.
        unfold combine_aux at 2.
        simpl.
        apply maymapto_find in maps2.
        rewrite maps2.
        clear maps2.
        apply Sorting.sort_inv in lsorted.
        destruct lsorted as [tsorted k'lt].
        set (m'mapsto := maymapto_add_1 k' (match e2 with
                    | Some e' => f e e'
                    | None => e
                    end) m2).

        set (m':=(M.add k' (match e2 with
                    | Some e' => f e e'
                    | None => e
                    end) m2)) in * |- *.
        generalize m'mapsto.
        generalize m'.
        clear m' m'mapsto maps1 e1in.
        induction l as [|[k0 e0] t0].
          intros.
          simpl.
          exact m'mapsto.

          intros.
          simpl.
          unfold combine_aux at 2.
          simpl.
          apply Sorting.sort_inv in tsorted.
          apply IHt0.
            destruct tsorted.
            assumption.

            apply Sorting.lelistA_inv in k'lt.
            destruct tsorted as [_ le0].
            destruct le0.
              apply Sorting.nil_leA.

              apply Sorting.cons_leA.
              unfold M.lt_key in *.
              simpl in *.
              apply M.E.lt_trans with (y:=k0); assumption.

              apply maymapto_add_2.
                apply Sorting.lelistA_inv in k'lt.
                unfold M.lt_key in k'lt.
                simpl in k'lt.
                apply M.E.lt_not_eq in k'lt.
                unfold not.
                intro H.
                apply M.E.eq_sym in H.
                apply k'lt.
                auto.

              assumption.

        (* neq case *)
        simpl.
        apply IHl.
          right.
          exists e1'.
          split; [reflexivity|assumption].

          unfold combine_aux.
          apply maymapto_add_2.
          (* Prove that because k is in the tail, it isn't k' *)
          intro k'keq.
          apply (sorted_head_lowest (k,e1') (k',e) l lsorted) in intail.
          unfold M.lt_key in intail.
          simpl in intail.
          apply M.E.lt_not_eq in intail.
          apply M.E.eq_sym in k'keq.
          contradiction.

          assumption.

          apply Sorting.sort_inv in lsorted.
          apply (proj1 lsorted).
Qed.

Lemma combine_2 : forall k m1 m2,
  M.In k (combine m1 m2) -> M.In k m1 \/ M.In k m2.
Proof.
  intros k m1 m2 [comb_val comb_mapsto].
  case_eq (M.mem k m1).
    intro in_m1.
    auto using M.mem_2.

    intro notmem_m1.
    assert (notin_m1 : ~M.In k m1) by (intro H; apply M.mem_1 in H; rewrite notmem_m1 in H; discriminate).
    assert (notin_em1 : ~(exists v,InA (M.eq_key_elt (elt:=elt)) (k,v) (M.elements m1))).
    intros [v inm1]. destruct notin_m1. exists v. apply M.elements_2. assumption.
    clear notmem_m1 notmem_m1.  right.
    unfold combine in comb_mapsto.
    rewrite M.fold_1 in comb_mapsto.
    set (m2':=m2) in comb_mapsto.
    assert (Hm2 : M.In k m2' -> M.In k m2) by auto.
    revert m2' Hm2 comb_mapsto.
    induction (M.elements m1).
      intros.
      simpl in *.
      apply Hm2.
      exists comb_val.
      auto.

      intros.
      destruct a as [ka va].
      simpl in comb_mapsto.
      apply IHl with (m2':= combine_aux ka va m2').
        intros [v inl].
        destruct notin_em1.
        exists v.
        right.
        assumption.

        intros [v mapsv].
        apply Hm2.
        exists v.
        unfold combine_aux in mapsv.
        eapply M.add_3 with (x:=ka).
          intro keq. destruct notin_em1.
          exists va. left. split; auto.

          apply mapsv.

        assumption.
Qed.

Lemma combine_3 : forall k m1 m2,
  M.In k m1 -> M.In k (combine m1 m2).
Proof.
intros k m1 m2 [v1 mapsto1].
assert (exists v, maymapto k v m2).
  unfold maymapto. case_eq (M.mem k m2); intro.
    apply M.mem_2 in H.
    destruct H as [v2 maps2].
    exists (Some v2). right. exists v2. tauto.

    exists (None (A:=elt)). left.  split; auto.
    intro. apply M.mem_1 in H0. rewrite H in H0. discriminate.
destruct H as [v2' may2].
destruct (combine_1 m1 m2 k (Some v1) v2') as [[bad _]|[v [veq maps]]].
  right. exists v1. tauto.

  assumption.

  simpl in bad. discriminate.

  exists v. assumption.
Qed.

Lemma combine_4 : forall k m1 m2,
  M.In k m2 -> M.In k (combine m1 m2).
Proof.
intros k m1 m2 [v2 mapsto2].
assert (exists v, maymapto k v m1).
  unfold maymapto. case_eq (M.mem k m1); intro.
    apply M.mem_2 in H.
    destruct H as [v1 maps1].
    exists (Some v1). right. exists v1. tauto.

    exists (None (A:=elt)). left.  split; auto.
    intro. apply M.mem_1 in H0. rewrite H in H0. discriminate.
destruct H as [v1' may1].
destruct (combine_1 m1 m2 k v1' (Some v2)) as [[bad _]|[v [veq maps]]].
  assumption.

  right. exists v2. tauto.

  destruct v1'; simpl in bad; discriminate.

  exists v. assumption.
Qed.

End Combine.

Implicit Arguments combine [elt].
Implicit Arguments combine_1 [elt f].
Implicit Arguments combine_2 [elt f].
Implicit Arguments combine_3 [elt f].
Implicit Arguments combine_4 [elt f].

End FMapCombine.

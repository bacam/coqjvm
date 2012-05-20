Require Import Arith.
Require Import OrderedTypeEx.
Require Import FMapPositive.
Require Import ZArith.
Require Import OptionExt.

Definition addr_t := positive.

Definition positive_eq_dec : forall (x y:positive), {x=y}+{x<>y}.
decide equality.
Defined.

Module Type HEAPOBJECT.
Parameter t : Type.
End HEAPOBJECT.

Open Scope positive_scope.

Module Type HEAP.

Parameter obj : Type.
Definition addr := addr_t.

Parameter t : Type.

(* Constants and operations *)
Parameter empty_heap : t.
Parameter lookup : t -> addr_t -> option obj.
Parameter update : t -> addr_t -> obj -> option t.
Parameter new : t -> obj -> t * addr_t.
Parameter lookup_informative : forall h a, {o : obj | lookup h a = Some o} + {lookup h a = None}.

(* Properties *)
Hypothesis lookup_update : forall s n v s', update s n v = Some s' -> lookup s' n = Some v.
Hypothesis lookup_empty : forall n, lookup empty_heap n = None.
Hypothesis indep_lookup : forall s n v s' n' v', update s n v = Some s' -> lookup s n' = Some v' -> n' <> n -> lookup s' n' = Some v'.
Hypothesis indep_lookup_2 : forall s s' n n' v v', update s n v = Some s' -> lookup s' n' = Some v' -> n' <> n -> lookup s n' = Some v'.
Hypothesis new_was_None : forall s v s' l, new s v = (s',l) -> lookup s l = None.
Hypothesis new_lookup : forall s v s' l, new s v = (s', l) -> lookup s' l = Some v.
Hypothesis new_preserves : forall s v s' l l' v', new s v = (s', l) -> lookup s l' = Some v' -> lookup s' l' = Some v'.
Hypothesis new_preserves_2 : forall s v s' l l' v', new s v = (s', l) -> lookup s' l' = Some v' -> l <> l' -> lookup s l' = Some v'.
Hypothesis update_ok : forall s n v v', lookup s n = Some v -> exists s', update s n v' = Some s'.
Hypothesis new_elim : forall s v, exists s', exists l', new s v = (s', l').

End HEAP.

Module MkHeap (Ob : HEAPOBJECT) <: HEAP with Definition obj := Ob.t.

Definition obj := Ob.t.
Definition addr := addr_t.

(*Module Key.
Definition t := nat.
Definition eq_dec : forall (a b:t), {a=b}+{a<>b}.
decide equality.
Defined.
End Key.*)

Definition heap_invariant :=
  fun (h:PositiveMap.t obj) max => forall n, (nat_of_P n >= nat_of_P max)%nat -> PositiveMap.find n h = None.

Record heap_t : Type := mkHeap
 { max_addr        : positive
 ; actual_heap     : PositiveMap.t obj
 ; max_unallocated : heap_invariant actual_heap max_addr
 }.

Definition t := heap_t.

Lemma find_4 : forall (h : PositiveMap.t obj) a,
 (forall o, ~PositiveMap.MapsTo a o h) ->
 PositiveMap.find a h = None.
intros h a not_there. destruct (option_dec (PositiveMap.find a h)) as [[o o_exists] | no_o].
 elimtype False. apply (not_there o). apply PositiveMap.find_2. apply o_exists.
 apply no_o.
Save.

Lemma find_5 : forall (h : PositiveMap.t obj) a,
 PositiveMap.find a h = None ->
 (forall o, ~PositiveMap.MapsTo a o h).
intros h a find_None o.
unfold not. intro.
rewrite (PositiveMap.find_1 H) in find_None. discriminate.
Save.

Lemma find_empty : forall n, PositiveMap.find n (PositiveMap.empty obj) = None.
intros. apply find_4. apply PositiveMap.empty_1.
Save.

Lemma empty_has_invariant : heap_invariant (PositiveMap.empty obj) xH.
unfold heap_invariant. intros. apply find_empty.
Save.

Definition empty_heap := mkHeap 1 (PositiveMap.empty obj) empty_has_invariant.

Definition lookup : t -> addr -> option obj :=
  fun h a => PositiveMap.find a (actual_heap h).

Lemma lookup_empty : forall n, lookup empty_heap n = None.
intros. unfold lookup. unfold empty_heap. simpl. apply find_empty.
Save.

Lemma find_None_add : forall (h:PositiveMap.t obj) a n o,
 a <> n ->
 PositiveMap.find n h = None ->
 PositiveMap.find n (PositiveMap.add a o h) = None.
intros h a n o a_neq_n n_nin_h.
apply find_4. intro o'.
unfold not. intro in_added. 
assert (PositiveMap.MapsTo n o' h \/ a = n).
 destruct (PositiveMap.E.compare a n).
  left. eapply PositiveMap.add_3.
   apply PositiveMap.E.lt_not_eq. apply l.
   apply in_added.
  right. assumption.
  left. eapply PositiveMap.add_3.
   unfold not. intros. refine (PositiveMap.E.lt_not_eq l _). apply PositiveMap.E.eq_sym. apply H.
   apply in_added.
destruct H.
 rewrite (PositiveMap.find_1 H) in n_nin_h. discriminate.
 contradiction.
Save.

Lemma update_preserves_invariant : forall m (h:PositiveMap.t obj) a o,
  ((exists o', PositiveMap.find a h = Some o') ->
   (forall n, nat_of_P n >= nat_of_P m -> PositiveMap.find n h = None) ->
   forall n, nat_of_P n >= nat_of_P m -> PositiveMap.find n (PositiveMap.add a o h) = None)%nat.
intros m h a o L Iold n GE.
apply find_None_add.
 unfold not. intro. subst.  destruct L as [o' o'_exists]. rewrite Iold in o'_exists.
  discriminate.
  assumption.
 auto.
Save.

Definition lookup_informative_Prop : forall (h:PositiveMap.t obj) a, { exists o, PositiveMap.find a h = Some o } + { PositiveMap.find a h = None }.
intros. destruct (PositiveMap.find a h). 
 left. exists o. trivial.
 right. trivial.
Defined.

Definition lookup_informative : forall h a, { o : obj | lookup h a = Some o } + { lookup h a = None }.
intros. destruct (lookup h a). 
 left. exists o. trivial.
 right. trivial.
Defined.

Definition update : t -> addr -> obj -> option t :=
  fun h a o => match h with
  | mkHeap m h P =>
     match lookup_informative_Prop h a with
     | left H => Some (mkHeap m (PositiveMap.add a o h) (update_preserves_invariant m h a o H P))
     | right _ => None
     end
  end.

Lemma new_preserves_invariant : forall m (h:PositiveMap.t obj) o,
 ((forall n, nat_of_P n >= nat_of_P m -> PositiveMap.find n h = None) ->
  forall n, nat_of_P n >= nat_of_P (Psucc m) -> PositiveMap.find n (PositiveMap.add m o h) = None)%nat.
intros m h o H n GT.
rewrite nat_of_P_succ_morphism in GT. 
apply find_None_add.
 unfold not. intros. subst. omega.
 auto with arith.
Save.

Definition new : t -> obj -> t * addr :=
 fun h o => match h with
 | mkHeap m h P =>
    let new_addr := m in
    let new_max := Psucc m in
     (mkHeap new_max (PositiveMap.add new_addr o h) (new_preserves_invariant m h o P), new_addr)
 end.

Lemma lookup_update : forall s n v s',
  update s n v = Some s' ->
  lookup s' n = Some v.
unfold lookup. unfold update. intros. 
destruct s. destruct (lookup_informative_Prop actual_heap0 n) as [[ob ob_exists] | not_exists].
 inversion H. subst. simpl. apply PositiveMap.find_1. apply PositiveMap.add_1. apply PositiveMap.E.eq_refl.
 discriminate.
Save.

Lemma indep_lookup : forall s n v s' n' v',
  update s n v = Some s' ->
  lookup s n' = Some v' ->
  n' <> n ->
  lookup s' n' = Some v'.
unfold update. unfold lookup. intros.
destruct s. destruct (lookup_informative_Prop actual_heap0 n) as [[o o_exists] | not_exists].
 inversion H. subst. simpl in *. apply PositiveMap.find_1. apply PositiveMap.add_2.
  congruence.
  apply PositiveMap.find_2. apply H0.
 discriminate.
Save.

Lemma indep_lookup_2 : forall s s' n n' v v',
  update s n v = Some s' ->
  lookup s' n' = Some v' ->
  n' <> n ->
  lookup s n' = Some v'.
unfold update. unfold lookup. intros.
destruct s. destruct (lookup_informative_Prop actual_heap0 n) as [[o o_exists] | not_exists].
 inversion H. subst. simpl in *. apply PositiveMap.find_1. eapply PositiveMap.add_3. 
  unfold not. intros. apply H1. symmetry. apply H2. 
  apply PositiveMap.find_2. apply H0.
 discriminate.
Save.
Implicit Arguments indep_lookup_2 [s s' n n' v v'].

Lemma new_was_None : forall s v s' l,
  new s v = (s',l) ->
  lookup s l = None.
unfold new. unfold lookup. intros.
destruct s. inversion H. subst.
simpl. apply max_unallocated0. auto with arith.
Save.

Lemma new_lookup : forall s v s' l,
  new s v = (s', l) ->
  lookup s' l = Some v.
unfold new. unfold lookup. intros. destruct s.
inversion H. simpl. subst. apply PositiveMap.find_1. apply PositiveMap.add_1. apply PositiveMap.E.eq_refl.
Save.

Lemma new_preserves : forall s v s' l l' v',
  new s v = (s', l) ->
  lookup s l' = Some v' ->
  lookup s' l' = Some v'.
unfold new. unfold lookup. intros.
destruct s. inversion H. subst. simpl in *.
apply PositiveMap.find_1. apply PositiveMap.add_2.
 unfold not. intros. rewrite (max_unallocated0 l') in H0. 
  discriminate.
  change PositiveMap.E.eq with PositiveOrderedTypeBits.eq in H1. unfold PositiveOrderedTypeBits.eq in H1. subst. auto with arith.
 apply PositiveMap.find_2. apply H0.
Save.

Lemma new_preserves_2 : forall s v s' l l' v',
  new s v = (s', l) ->
  lookup s' l' = Some v' ->
  l <> l' ->
  lookup s l' = Some v'.
unfold new. unfold lookup. intros. destruct s.
inversion H. subst. simpl in *. apply PositiveMap.find_1. eapply PositiveMap.add_3.
 apply H1.
 apply PositiveMap.find_2. apply H0.
Save.

Lemma update_ok : forall s n v v',
  lookup s n = Some v ->
  exists s', update s n v' = Some s'.
unfold lookup. unfold update. intros. 
destruct s. destruct (lookup_informative_Prop actual_heap0 n) as [[o o_exists] | not_exists].
 match goal with [ |- ex (fun _ => Some ?s = _) ] => exists s; reflexivity end.
 simpl in H. rewrite not_exists in H. discriminate.
Save.

Lemma new_elim : forall s v,
  exists s', exists l', new s v = (s', l').
intros. destruct (new s v). exists t0. exists a. reflexivity.
Save.

End MkHeap.

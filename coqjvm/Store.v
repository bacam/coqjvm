Require Import FMaps.
Require FMapAVL.
Require Import OptionExt.
Require Import BoolExt.
Require Import Wf_nat.
Require Import StoreIface.
Require Import Arith.
Require Import Setoid.
Require ChainRecurse.

Module Type STORAGEOBJECT.
Parameter t : Type.
End STORAGEOBJECT.

Module MkStore (Key0 : OrderedType) (Ob : STORAGEOBJECT)
             : STORE with Definition key := Key0.t
                     with Definition object := Ob.t
                     with Module Key := Key0.

Module Key := Key0.
Module St : FMapInterface.S with Module E:= Key := FMapAVL.Make Key.
Module SFacts := FMapFacts.Facts St.

Add Relation Key.t Key.eq
 reflexivity proved by Key.eq_refl
 symmetry proved by Key.eq_sym
 transitivity proved by Key.eq_trans
as Key_eq_rel.

Definition key := Key.t.
Definition object := Ob.t.
Definition t := St.t object.

Definition empty : t := St.empty object.

Definition lookup (l:t) (k:key) : option object := St.find k l.

Lemma lookup_eq : forall s k1 k2, Key.eq k1 k2 -> lookup s k1 = lookup s k2.
unfold lookup. intros.
destruct (option_dec (St.find k1 s)) as [[o o_exists] | no_o].
 (* it is in under k1 *)
 assert (St.MapsTo k2 o s). eapply St.MapsTo_1. apply H. apply St.find_2. assumption.
 rewrite (St.find_1 H0). assumption.
 (* it is not in under k1 *)
 destruct (option_dec (St.find k2 s)) as [[o' o'_exists] | no_o'].
  (* it is in under k2: impossible *)
  assert (St.MapsTo k1 o' s). eapply St.MapsTo_1. change St.E.eq with Key.eq. symmetry. apply H. apply St.find_2. assumption.
  rewrite (St.find_1 H0) in no_o. discriminate.
  (* not in under k2 *)
  congruence.
Save.    

Definition lookup_informative : forall l k, { o : object | lookup l k = Some o } + { lookup l k = None }.
intros. destruct (lookup l k). left. exists o. trivial. right. trivial.
Defined.

Module Store_chain_recurse := ChainRecurse.ChainRecurse St.

Definition chain_fix (T:key->Type)
  (s:t) 
  (err_cycle : forall k, T k)
  (err_notfound : forall k, T k)
  (f:(forall k:key, T k) -> forall k:key, {e : object | lookup s k = Some e}  -> T k)
  (k:key) :=
  Store_chain_recurse.cfix T err_cycle err_notfound f k.

Definition update (l:t) (k:key) (b:object) : t := St.add k b l.

Lemma lookup_update : forall s k b, lookup (update s k b) k = Some b.
unfold lookup. unfold update.
intros. apply St.find_1. apply St.add_1. apply Key.eq_refl.
Save.

(*Lemma update_update : forall s k o1 o2, update (update s k o1) k o2 = update s k o2.
unfold update. intros.


intros. induction s. 
 simpl. destruct (Key.eq_dec k k).
  reflexivity.
  elimtype False. apply n. reflexivity.
 simpl. destruct a.
 destruct (Key.eq_dec k k0). 
  simpl. destruct (Key.eq_dec k k).
   reflexivity.
   elimtype False. apply n. reflexivity.
  simpl. destruct (Key.eq_dec k k0).
   elimtype False. apply (n e).
   rewrite IHs. reflexivity.
Save.*)

(*
Definition store_eq : t -> t -> Prop :=
  fun a b => forall k x, (lookup a k = Some x -> lookup b k = Some x) /\ (lookup b k = Some x -> lookup a k = Some x).

Lemma store_eq_refl : forall x, store_eq x x.
unfold store_eq. auto.
Save.

Lemma store_eq_symm : forall a b, store_eq a b -> store_eq b a.
unfold store_eq. intros. destruct (H k x). auto. 
Save. 

Lemma store_eq_trans : forall a b c, store_eq a b -> store_eq b c -> store_eq a c. 
unfold store_eq. intros. 
destruct (H k x).
destruct (H0 k x).
auto.
Save.

Lemma store_eq_cong : forall k o x y, store_eq x y -> store_eq ((k,o)::x) ((k,o)::y).
unfold store_eq. intros. simpl.
destruct (Key.eq_dec k0 k); auto.
Save.

Lemma indep_update : forall a k1 x1 k2 x2, k1 <> k2 -> store_eq (update (update a k1 x1) k2 x2) (update (update a k2 x2) k1 x1).
intros. induction a.
 simpl. destruct (Key.eq_dec k1 k2). 
  elimtype False. apply (H e).
  destruct (Key.eq_dec k2 k1). 
   elimtype False. apply H. symmetry. assumption.
   unfold store_eq. simpl. intros. 
   destruct (Key.eq_dec k k1). 
    subst. destruct (Key.eq_dec k1 k2). 
     contradiction.
     auto.
    destruct (Key.eq_dec k k2); auto.
 simpl. destruct a.
  destruct (Key.eq_dec k1 k). 
   subst. destruct (Key.eq_dec k2 k). 
    elimtype False. apply H. symmetry. assumption.
    simpl. destruct (Key.eq_dec k2 k). 
     contradiction.
     destruct (Key.eq_dec k k).
      apply store_eq_refl.
      elimtype False. apply n1. reflexivity.
   simpl. destruct (Key.eq_dec k2 k).
    subst. simpl. destruct (Key.eq_dec k k).
     destruct (Key.eq_dec k1 k).
      contradiction.
      apply store_eq_refl.
     elimtype False. apply n0. reflexivity.
    simpl. destruct (Key.eq_dec k1 k).
     contradiction.
     apply store_eq_cong. assumption.
Save.
*)

Lemma forward : forall (A B:Prop), (A <-> B) -> A -> B.
tauto.
Save.

Lemma backward : forall (A B:Prop), (A <-> B) -> B -> A.
tauto.
Save.

Implicit Arguments forward [A B].
Implicit Arguments backward [A B].

Lemma indep_lookup : forall c n1 n2 a, ~(Key.eq n1 n2) -> lookup (update c n1 a) n2 = lookup c n2.
unfold update. unfold lookup.
intros. destruct (option_dec (St.find n2 c)) as [[o o_exists] | no_o].
 rewrite o_exists. apply St.find_1. apply St.add_2. assumption. apply St.find_2. apply o_exists.
 rewrite no_o.
 assert (~St.In n2 c). apply (backward (SFacts.not_find_mapsto_iff c n2)). assumption.
 apply (forward (SFacts.not_find_mapsto_iff (St.add n1 a c) n2)).
 unfold not. intro. apply H0. 
 destruct (forward (SFacts.add_in_iff c n1 n2 a) H1); intuition.
Save.

(*Lemma lookup_None : forall h x g, lookup (x::h) g = None -> lookup h g = None.
intros. destruct x. simpl in H. destruct (Key.eq_dec g k).
 discriminate.
 assumption.
Save.*)

(*
Lemma store_eq_update_cong : forall x y k o, store_eq x y -> store_eq (update x k o) (update y k o).
unfold store_eq. intros. 
destruct (Key.eq_dec k k0). 
 subst. repeat (rewrite lookup_update). auto.
 repeat (rewrite indep_lookup; try assumption). auto.
Save.
*)
Lemma indep_lookup_2 : forall c n1 n2 a x, ~(Key.eq n1 n2) -> lookup (update c n1 a) n2 = Some x -> lookup c n2 = Some x.
intros. rewrite <- (indep_lookup c n1 n2 a); assumption.
Save.

Definition remove (k:key) (l:t) : t := St.remove k l.

Definition remove_by (f:key -> bool) (m:t) : t := St.fold (fun k o m => if f k then m else St.add k o m) m (St.empty object).

Lemma not_in_add : forall k k' (o:object) s,
 ~Key.eq k' k ->
 St.find k s = None ->
 St.find k (St.add k' o s) = None.
intros.
destruct (option_dec (St.find k (St.add k' o s))) as [[o' find_res] | find_res].
 assert (St.find k s = Some o').
  apply St.find_1. eapply St.add_3. apply H. apply St.find_2. apply find_res.
 rewrite H1 in H0. discriminate.
 assumption.
Save.  

Hint Resolve not_in_add.

(*
Lemma neq_symm : forall k k', ~Key.eq k k' -> ~Key.eq k' k.
unfold not. auto.
Save.*)

Lemma remove_by_lookup : forall l k f, (forall k k', Key.eq k k' -> f k = f k') -> f k = true -> lookup (remove_by f l) k = None.
unfold remove_by. unfold lookup.
intros. rewrite St.fold_1.
set (s:=St.empty object).
assert (not_in_s:St.find k s = None).
 destruct (option_dec (St.find k (St.empty object))) as [[o o_exists] | no_o].
  elimtype False. refine (St.empty_1 _). apply St.find_2. apply o_exists.
  assumption.
generalize s not_in_s. clear s not_in_s. induction (St.elements l); intros.
 (* nil *)
 simpl. assumption.
 (* cons *)
 simpl. destruct a. simpl. destruct (Key.compare k k0).
  (* LT *)
  apply IHl0. destruct (bool_dec (f k0)); rewrite H1; eauto.
  (* EQ *)
  apply IHl0. destruct (bool_dec (f k0)); rewrite H1; eauto.
   rewrite (H _ _ e) in H0. rewrite H1 in H0. discriminate.
  (* GT *)
  apply IHl0. destruct (bool_dec (f k0)); rewrite H1; eauto.
Save.

Lemma remove_lookup : forall l k, lookup (remove k l) k = None.
unfold lookup. unfold remove. intros.
destruct (option_dec (St.find k (St.remove k l))) as [[o o_exists] | no_o].
 elimtype False. refine (St.remove_1 (elt:=object) _ _).
  apply Key.eq_refl.
  exists o. apply St.find_2. eassumption.
 assumption.
Save.

Lemma remove_lookup_2 : forall l k1 k2, lookup l k1 = None -> lookup (remove k2 l) k1  = None.
unfold remove. unfold lookup. intros.
destruct (option_dec (St.find k1 (St.remove k2 l))) as [[o o_exists] | no_o].
 elimtype False. refine (backward (SFacts.not_find_mapsto_iff l k1) _ _).
  assumption.
  exists o. eapply St.remove_3. apply St.find_2. eassumption.
 assumption.
Save.

Lemma remove_lookup_3 : forall k1 k2 c o, lookup (remove k1 c) k2 = Some o -> lookup c k2 = Some o.
unfold remove. unfold lookup. intros.
eapply St.find_1. eauto using St.find_2, St.remove_3.
Save.

Lemma remove_lookup_4 : forall c nm nm' x, lookup c nm = Some x -> ~Key.eq nm' nm -> lookup (remove nm' c) nm = Some x.
unfold remove. unfold lookup. intros.
eapply St.find_1. eauto using St.find_2, St.remove_2.
Save.

(*
Lemma commute_remove : forall s x y, remove x (remove y s) = remove y (remove x s).
intros. induction s.
 reflexivity. 
 simpl. destruct a. destruct (Key.eq_dec y k).
  subst. destruct (Key.eq_dec x k).
   subst. assumption.
   rewrite IHs. simpl. destruct (Key.eq_dec k k).
    reflexivity.
    elimtype False. apply n0. reflexivity.
  simpl. destruct (Key.eq_dec x k). 
   assumption.
   simpl. destruct (Key.eq_dec y k).
    contradiction.
    rewrite IHs. reflexivity.
Save.*)

(*
Lemma lookup_cons : forall a b c, lookup ((a,b)::c) a = Some b.
intros. simpl. destruct (Key.eq_dec a a). 
 reflexivity.
 elimtype False. apply n. reflexivity.
Save.

Lemma lookup_cons_neq : forall a a' b c, a' <> a -> lookup ((a,b)::c) a' = lookup c a'.
intros. simpl. destruct (Key.eq_dec a' a).
 contradiction.
 reflexivity.
Save.

Lemma update_cons : forall a b b' c, update ((a,b)::c) a b' = (a,b')::c.
intros. simpl. destruct (Key.eq_dec a a).
 reflexivity.
 elimtype False. apply n. reflexivity.
Save.

Lemma remove_update : forall s k o, store_eq (update (remove k s) k o) (update s k o).
intros. induction s. 
 unfold store_eq. simpl. intros. destruct (Key.eq_dec k0 k); auto.
 destruct a. simpl. destruct (Key.eq_dec k k0). 
  unfold store_eq. intros. simpl. destruct (Key.eq_dec k1 k). 
   subst. rewrite lookup_update. auto.
   rewrite indep_lookup. split; intros. 
    eapply remove_lookup_3. apply H. 
    apply remove_lookup_4. assumption. unfold not. intros. apply n. symmetry. assumption.
    unfold not. intros. apply n. symmetry. assumption.
   unfold store_eq. intros. simpl. destruct (Key.eq_dec k k0).
    contradiction.
    destruct (Key.eq_dec k1 k0). 
     subst. rewrite lookup_cons. auto.
     rewrite lookup_cons_neq. apply IHs. assumption.
Save.
*)


(*Fixpoint add_all (s:t) (f:object->key) (l:list object) {struct l} : t :=
  match l with
  | nil   => s
  | o::os => add_all (update s (f o) o) f os
  end.

Fixpoint check_all (s:t) (f:key->object->bool) {struct s} : bool :=
  match s with
  | nil => true
  | (k,o)::s => if f k o then check_all s f else false
  end.

Lemma check_all_correct : forall s f (P:key->object->Prop),
  (forall k o, f k o = true -> P k o) ->
  check_all s f = true -> (forall k o, lookup s k = Some o -> P k o).
intros.
induction s. 
 discriminate.
 destruct a. simpl in * |- *. destruct_bool (f k0 o0) H2 H0.
 destruct (Key.eq_dec k k0). 
  inversion H1. subst. auto.
  auto.
Save.

Fixpoint fold (A:Set) (store:t) (f:key -> object -> A -> A) (a:A) {struct store} : A :=
  match store with
  | nil           => a
  | (k, o)::store => f k o (fold A store f a)
  end.
Implicit Arguments fold [A].*)

Definition elements := @St.elements object.

Definition eq_key_obj := fun x y : key * object => Key.eq (fst x) (fst y) /\ snd x = snd y.

Lemma elements_1 : forall s k o,
  lookup s k = Some o -> InA eq_key_obj (k,o) (elements s).
intros. unfold elements. change eq_key_obj with (@St.eq_key_elt object). apply St.elements_1. apply St.find_2. apply H.
Save.  

Lemma elements_2 : forall s k o,
  InA eq_key_obj (k,o) (elements s) -> lookup s k = Some o.
intros. unfold lookup. apply St.find_1. apply St.elements_2. apply H.
Save.

(* Recursion over removals *)

Lemma lookup_empty : forall k, lookup empty k = None.
intros. unfold lookup. unfold empty. 
destruct (option_dec (St.find k (St.empty object))) as [[o o_exists] | no_o].
 elimtype False. refine (St.empty_1 _). eapply St.find_2. apply o_exists.
 assumption.
Save.

Lemma elements_empty : elements empty = nil.
case_eq (elements empty). auto.
intros. destruct p as [x y]. assert (St.MapsTo x y empty).
 apply St.elements_2. unfold elements in H. rewrite H. apply InA_cons_hd. unfold St.eq_key_elt. simpl. split. apply Key0.eq_refl. reflexivity.
 apply St.empty_1 in H0. contradiction.
Qed.

(*
Lemma remove_dec_size_aux : forall p nm, length (St.elements (remove nm p)) <= length (St.elements p).
intros. induction p.
auto with arith.
destruct a. simpl. destruct (Key.eq_dec nm k); simpl; auto with arith. 
Save.*)

Inductive wf_removals : t -> Prop :=
| wfr_empty : forall m,
   (forall k, lookup m k = None) ->
   wf_removals m
| wfr_rem : forall s,
   (forall nm c,
      lookup s nm = Some c ->
      wf_removals (remove nm s)) ->
   wf_removals s.

Scheme wf_removals_ind2 := Induction for wf_removals Sort Prop.

Definition wf_removals_inv : forall s nm c,
  lookup s nm = Some c ->
  wf_removals s ->
  wf_removals (remove nm s)
  :=
fun (s : t) (nm : key) (c : object) (H : lookup s nm = Some c)
  (H0 : wf_removals s) =>
match
  H0 in (wf_removals t)
  return (lookup t nm = Some c -> wf_removals (remove nm t))
with
| wfr_empty m H1 =>
    fun H2 : lookup m nm = Some c =>
    let H3 :=
      eq_ind (lookup m nm) (fun o : option object => o = Some c) H2 None
        (H1 nm) in
    let H4 :=
      eq_ind None
        (fun e : option object =>
         match e with
         | Some _ => False
         | None => True
         end) I (Some c) H3 in
    False_ind (wf_removals (remove nm m)) H4
| wfr_rem s0 H1 => fun H2 : lookup s0 nm = Some c => H1 nm c H2
end H.
Implicit Arguments wf_removals_inv [s nm c].

Inductive In2 (x : key) : list (key*object) -> Prop :=
  | In2_cons_hd : forall d y l, Key.eq x y -> In2 x ((y,d) :: l)
  | In2_cons_tl : forall d y l, In2 x l -> In2 x ((y,d) :: l).

Add Morphism In2
 with signature Key.eq ==> (eq (A:=list (key*object))) ==> iff
 as In2_mor.
induction y0.
 intuition; inversion H0.
 intuition.
  inversion H2.
   apply In2_cons_hd. rewrite <- H. assumption.
   apply In2_cons_tl. auto.
  inversion H2.
   apply In2_cons_hd. rewrite H. assumption.
   apply In2_cons_tl. auto.
Save.

Module KeyFacts := OrderedTypeFacts Key.

Add Morphism Key.lt
 with signature Key.eq ==> Key.eq ==> iff
 as lt_mor.
intuition eauto using KeyFacts.lt_eq, KeyFacts.eq_lt. 
Save.

Lemma sort_lelist : forall l k o k' o',
 sort (St.lt_key (elt:=object)) ((k',o')::l) ->
 lelistA (St.lt_key (elt:=object)) (k,o) ((k',o')::l) ->
 lelistA (St.lt_key (elt:=object)) (k,o) l.
intros. inversion H. inversion H4.
 constructor.
 constructor. inversion H0. destruct b. unfold St.lt_key in *. simpl in *. eapply Key.lt_trans; eauto.
Save.

Lemma sort_not_in : forall l o k,
 sort (St.lt_key (elt:=object)) l ->
 lelistA (St.lt_key (elt:=object)) (k,o) l ->
 In2 k l ->
 False.
induction l; intros.
 (* l is nil *)
 inversion H1.
 (* l is cons *)
 destruct a as [k' o']. inversion H1.
  inversion H0. unfold St.lt_key in H7. simpl in H7. apply (Key.lt_not_eq H7 H3).
  inversion H. eapply IHl.
   apply H8.
   eapply sort_lelist; eauto.
   apply H3.
Save.

Lemma list_eq_size_aux : forall (l1 l2 : list (key * object)),
 (forall y, In2 y l1 -> In2 y l2) ->
 (forall y,  In2 y l2 -> In2 y l1) ->
 sort (St.lt_key (elt:=object)) l1 ->
 sort (St.lt_key (elt:=object)) l2 ->
 length l1 = length l2.
induction l1 as [|[k1 o1] l1]; intros.
 (* l1 is nil *)
 destruct l2 as [|[k2 o2] l2].
  (* l2 is nil *)
  reflexivity.
  (* l2 is cons: impossible *)
  assert (k2_in_nil:In2 k2 nil) by eauto using In2_cons_hd. inversion k2_in_nil.
 (* l1 is cons *)
 destruct l2 as [|[k2 o2] l2].
  (* l2 is nil: impossible *)
  assert (k1_in_nil:In2 k1 nil) by eauto using In2_cons_hd. inversion k1_in_nil.
  (* l2 is cons *)
  assert (Key.eq k1 k2).
   destruct (Key.compare k1 k2).
    (* k1 < k2 *)
    elimtype False. apply (sort_not_in ((k2,o2)::l2) o1 k1); eauto using cons_leA, In2_cons_hd. 
    (* k1 = k2 *)
    apply e.
    (* k2 < k1 *)
    elimtype False. apply (sort_not_in ((k1,o1)::l1) o2 k2); eauto using cons_leA, In2_cons_hd.
   inversion H1. subst.
   inversion H2. subst.
   simpl. apply (f_equal S). eapply IHl1.
    (* l1 is in l2 *)
    intros.
    assert (In2 y ((k2,o2)::l2)) by eauto using In2_cons_tl.
    inversion H5. 
     elimtype False. eapply sort_not_in.
      apply H6.
      apply H7.
      rewrite H3. rewrite <- H11. assumption.
     assumption.
    (* l2 is in l1 *)
    intros.
    assert (In2 y ((k1,o1)::l1)). apply H0. apply In2_cons_tl. apply H4.
    inversion H5. 
     elimtype False. eapply sort_not_in.
      apply H8.
      apply H9.
      rewrite <- H3. rewrite <- H11. assumption.
     assumption.
    (* l1 is sorted *)
    assumption.
    (* l2 is sorted *)
    assumption.
Save.

Lemma lt_lelist : forall l k k',
  lelistA (St.lt_key (elt:=object)) k l ->
  St.lt_key k' k ->
  lelistA (St.lt_key (elt:=object)) k' l.
intros. inversion H; constructor.
 unfold St.lt_key in *. intuition eauto using Key.lt_trans.
Save.

Lemma lelist2 : forall l k o y,
  lelistA (St.lt_key (elt:=object)) (k,o) l ->
  In2 y l ->
  sort (St.lt_key (elt:=object)) l ->
  Key.lt k y.
induction l; intros.
 (* l is nil *)
 inversion H0.
 (* l is cons *)
 destruct a as [k' o'].
 inversion H0; subst.
  inversion H. rewrite H3. unfold St.lt_key in H4. simpl in H4. assumption.
  eapply IHl.
   eapply sort_lelist. apply H1. apply H.
   apply H3.
   inversion H1. assumption.
Save.

Lemma foo : forall l1 l2 x o,
 sort (St.lt_key (elt:=object)) ((x,o)::l2) ->
 (forall y, ~Key.eq x y -> In2 y ((x,o)::l2) -> In2 y l1) ->
 (forall y, In2 y l2 -> In2 y l1).
intros. apply H0.
 (* to show: x <> y *)
 assert (Key.lt x y). inversion H. eapply lelist2; eauto.
 apply Key.lt_not_eq. apply H2.
 (* to show: In2 y ((x,o)::l2) *)
 apply In2_cons_tl. assumption.
Save.

Lemma eq_le : forall x y, x = y -> x <= y.
intros. subst. auto with arith.
Save.

Lemma list_dec_size_aux : forall (l1 l2 : list (key * object)) x,
 (forall y, In2 y l1 -> In2 y l2) ->
 (forall y, ~Key.eq x y -> In2 y l2 -> In2 y l1) ->
 sort (St.lt_key (elt:=object)) l1 ->
 sort (St.lt_key (elt:=object)) l2 ->
 length l1 <= length l2.
induction l1; intros.
 (* l1 is nil *)
 auto with arith.
 (* l1 is cons *)
 destruct a as [k1 o1].
 destruct l2 as [|[k2 o2] l2].
  (* l2 is nil: impossible *)
  assert (In2 k1 nil). apply H. apply In2_cons_hd. apply Key.eq_refl. inversion H3.
  (* l2 is cons *)
  assert (Key.eq k1 k2 \/ (Key.eq x k2 /\ Key.lt k2 k1)).
   destruct (Key.compare k1 k2).
    (* k1 < k2 *)
    elimtype False. apply (sort_not_in ((k2,o2)::l2) o1 k1).
     apply H2.
     constructor. unfold St.lt_key. simpl. apply l.
     apply H. apply In2_cons_hd. apply Key.eq_refl.
    (* k1 = k2 *)
    left. apply e.
    (* k2 < k1 *)
    assert (Key.eq x k2 \/ ~Key.eq x k2).
     destruct (Key.compare x k2).
      right. apply Key.lt_not_eq. apply l0.
      left. assumption.
      right. unfold not. intro. refine (Key.lt_not_eq _ _). apply l0. symmetry. apply H3.
    destruct H3.
     right. auto.
     left. elimtype False. apply (sort_not_in ((k1,o1)::l1) o2 k2).
      apply H1.
      constructor. unfold St.lt_key. simpl. apply l.
      apply H0. apply H3. apply In2_cons_hd. apply Key.eq_refl.
   inversion H1. subst.
   inversion H2. subst.
   destruct H3.
    (* k1 = k2 *)
    simpl. apply le_n_S. eapply IHl1.
     (* l1 is in l2 *)
     intros.
     assert (In2 y ((k2,o2)::l2)). apply H. apply In2_cons_tl. apply H4.
     inversion H5.
      elimtype False. eapply sort_not_in.
       apply H6.
       apply H7.
       rewrite H3. rewrite <- H11. assumption.
      assumption.
     (* l2 is in l1 *)
     intros.
     assert (In2 y ((k1,o1)::l1)). apply H0. apply H4. apply In2_cons_tl. apply H5.
     inversion H10.
      elimtype False. eapply sort_not_in.
       apply H8.
       apply H9.
       rewrite <- H3. rewrite <- H12. assumption.
      assumption.
     (* l1 is sorted *)
     assumption.
     (* l2 is sorted *)
     assumption.
    (* x = k2 /\ k2 < k1 *)
    destruct H3.
    eapply le_trans.
     apply eq_le. eapply list_eq_size_aux.
      (* (k1,o1)::l1 in l2 *)
      intros.
      assert (In2 y ((k2,o2)::l2)). apply H. apply H5.
      inversion H10.
       (* y = k2 *)
       rewrite H12 in H5. elimtype False. inversion H5.
        apply (Key.lt_not_eq H4 H16).
        eapply (sort_not_in l1 o1 k2).
         apply H6.
         eapply lt_lelist. apply H7. unfold St.lt_key. simpl. apply H4.
         apply H16.
       (* y in l2 *)
       apply H12.
      (* l2 in (k1::o1) in l2 *)
      intros. eapply foo.
       apply H2.
       intros. apply H0. rewrite H3. apply H10. apply H11.
       apply H5.
      (* (k1,o1)::l1 sorted *)
      apply H1.
      (* l2 sorted *)
      apply H8.
     simpl. auto with arith.
Save.

Lemma list_dec_size : forall (l1 l2 : list (key * object)) x,
 In2 x l2 ->
 ~In2 x l1 ->
 (forall y, In2 y l1 -> In2 y l2) ->
 (forall y, ~Key.eq x y -> In2 y l2 -> In2 y l1) ->
 sort (St.lt_key (elt:=object)) l1 ->
 sort (St.lt_key (elt:=object)) l2 ->
 length l1 < length l2.
induction l1; intros.
 (* l1 is nil *)
 destruct l2 as [|[k2 o2] l2].
  (* l2 is nil : impossible *)
  inversion H.
  (* l2 is cons *)
  simpl. auto with arith.
 (* l1 is cons *)
 destruct a as [k1 o1].
 destruct l2 as [|[k2 o2] l2].
  (* l2 is nil: impossible *)
  assert (In2 k1 nil). apply H1. apply In2_cons_hd. apply Key.eq_refl. inversion H5.
  (* l2 is cons *)
  assert (Key.eq k1 k2 \/ (Key.eq x k2 /\ Key.lt k2 k1)).
   destruct (Key.compare k1 k2).
    (* k1 < k2 *)
    elimtype False. apply (sort_not_in ((k2,o2)::l2) o1 k1).
     apply H4.
     constructor. unfold St.lt_key. simpl. apply l.
     apply H1. apply In2_cons_hd. apply Key.eq_refl.
    (* k1 = k2 *)
    left. apply e.
    (* k2 < k1 *)
    assert (Key.eq x k2 \/ ~Key.eq x k2).
     destruct (Key.compare x k2).
      right. apply Key.lt_not_eq. apply l0.
      left. assumption.
      right. unfold not. intro. refine (Key.lt_not_eq _ _). apply l0. symmetry. apply H5.
    destruct H5.
     right. auto.
     left. elimtype False. apply (sort_not_in ((k1,o1)::l1) o2 k2).
      apply H3.
      constructor. unfold St.lt_key. simpl. apply l.
      apply H2. apply H5. apply In2_cons_hd. apply Key.eq_refl.
   inversion H3. subst.
   inversion H4. subst.
   destruct H5.
    (* k1 = k2 *)
    simpl. apply lt_n_S. eapply IHl1.
     (* x is still in l2 *)
     inversion H.
      rewrite <- H5 in H7. elimtype False. apply H0. apply In2_cons_hd. apply H7.
      apply H7.
     (* x is still not in l1 *)
     unfold not. intro. apply H0. apply In2_cons_tl. apply H6.
     (* l1 is in l2 *)
     intros.
     assert (In2 y ((k2,o2)::l2)). apply H1. apply In2_cons_tl. apply H6.
     inversion H7.
      elimtype False. eapply sort_not_in.
       apply H8.
       apply H9.
       rewrite H5. rewrite <- H13. assumption.
      assumption.
     (* l2 is in l1 *)
     intros.
     assert (In2 y ((k1,o1)::l1)). apply H2. apply H6. apply In2_cons_tl. apply H7.
     inversion H12.
      elimtype False. eapply sort_not_in.
       apply H10.
       apply H11.
       rewrite <- H5. rewrite <- H14. assumption.
      assumption.
     (* l1 is sorted *)
     assumption.
     (* l2 is sorted *)
     assumption.
    (* x = k2 /\ k2 < k1 *)
    destruct H5.
    replace (length ((k1,o1)::l1)) with (length l2).
     simpl. auto with arith.
     symmetry. eapply list_eq_size_aux.
      (* (k1,o1)::l1 in l2 *)
      intros.
      assert (In2 y ((k2,o2)::l2)). apply H1. apply H7.
      inversion H12.
       (* y = k2 *)
       rewrite H14 in H7. elimtype False. inversion H7.
        apply (Key.lt_not_eq H6 H18).
        eapply (sort_not_in l1 o1 k2).
         apply H8.
         eapply lt_lelist. apply H9. unfold St.lt_key. simpl. apply H6.
         apply H18.
       (* y in l2 *)
       apply H14.
      (* l2 in (k1::o1) in l2 *)
      intros. eapply foo.
       apply H4.
       intros. apply H2. rewrite H5. apply H12. apply H13.
       apply H7.
      (* (k1,o1)::l1 sorted *)
      apply H3.
      (* l2 sorted *)
      apply H10.
Save.

Definition size := fun m => length (St.elements (elt:=object) m).

Lemma InA_In2 : forall l o k,
 InA (St.eq_key_elt (elt:=object)) (k,o) l ->
 In2 k l.
induction l; intros.
 inversion H.
 destruct a as [k' o']. inversion H.
  unfold St.eq_key_elt in H1. simpl in H1. destruct H1. apply In2_cons_hd. assumption.
  apply In2_cons_tl. eauto.
Save.

Lemma In2_InA : forall l k,
 In2 k l ->
 exists o, InA (St.eq_key_elt (elt:=object)) (k,o) l.
induction l; intros.
 inversion H.
 destruct a as [k' o']. inversion H.
  exists o'. apply InA_cons_hd. split. apply H1. reflexivity.
  destruct (IHl k H1) as [o2 k_o2_in_l].
  exists o2. apply InA_cons_tl. assumption.
Save.

Lemma remove_dec_size : forall m k o,
 St.MapsTo k o m ->
 size (remove k m) < size m.
intros. unfold size. unfold remove.
eapply list_dec_size.
 (* k is in m *)
 eapply InA_In2. apply St.elements_1. apply H.
 (* k is not in the elements of m with k removed *)
 unfold not. intro.
 assert (St.In k (remove k m)).
  destruct (In2_InA _ _ H0) as [o' ko'_in_rem_k_m].
  exists o'. apply St.elements_2. assumption.
 refine (St.remove_1 _ H1). apply Key.eq_refl.
 (* inclusion of post-removal in pre *)
 intros.
 destruct (In2_InA _ _ H0) as [o' inA].
 eapply InA_In2.
 apply St.elements_1.
 eapply St.remove_3.
 eapply St.elements_2.
 apply inA.
 (* inclusion of pre in post-removal, except k *)
 intros.
 destruct (In2_InA _ _ H1) as [o' inA].
 eapply InA_In2.
 eapply St.elements_1.
 eapply St.remove_2.
  apply H0.
  apply St.elements_2. apply inA.
 (* sortedness of elements with removal *)
 apply St.elements_3.
 (* sortedness of elements *)
 apply St.elements_3.
Save.

Lemma size0_has_no_entries : forall m,
 0%nat = size m ->
 (forall k, lookup m k = None).
intros.
unfold size in H.
destruct (lookup_informative m k) as [[o k_exists] | no_o].
 (* k exists: impossible *)
 assert (InA (St.eq_key_elt (elt:=object)) (k,o) (St.elements m)).
  apply St.elements_1. apply St.find_2. apply k_exists.
 destruct (St.elements m).
  inversion H0.
  discriminate.
 (* no k: what we want *)
 assumption.
Save.

Lemma all_wf_removals : forall s, wf_removals s.
apply (well_founded_ind (well_founded_ltof _ size)).
intros.
destruct (O_or_S (size x)) as [[m x_Sm] | x_0].
 (* x has something in it *)
 apply wfr_rem. intros. apply H. unfold ltof. eapply remove_dec_size. apply St.find_2. apply H0.
 (* x is empty *)
 apply wfr_empty. apply size0_has_no_entries. assumption.
Save.

End MkStore.















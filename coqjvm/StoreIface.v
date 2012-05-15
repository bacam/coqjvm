Require Import OrderedType.

Module Type STORE.

Parameter key : Type.
Parameter object : Type.

Declare Module Key : OrderedType with Definition t := key.

Parameter t : Type.

Parameter empty : t.
Parameter lookup : t -> key -> option object.
Parameter lookup_informative : forall l k, {o : object | lookup l k = Some o} + {lookup l k = None}.
Parameter update : t -> key -> object -> t.
Parameter remove : key -> t -> t.
Parameter elements : t -> list (key * object).

Parameter remove_by : (key -> bool) -> t -> t.
(*Parameter check_all : t -> (key->object->bool) -> bool.*)

(** A fixed point operator for (non-cyclic) chains of lookups. *)
Parameter chain_fix : forall T:key->Type, forall s:t, (*cycle*) (forall k:key, T k) -> (*notfound*) (forall k:key, T k) -> ((forall k:key, T k) -> forall k:key, {e:object | lookup s k = Some e} -> T k) -> forall k:key, T k.

(* Some properties of the above *)
Parameter lookup_empty : forall k, lookup empty k = None.
Parameter lookup_update : forall s k b, lookup (update s k b) k = Some b.
Parameter indep_lookup : forall c n1 n2 a, ~Key.eq n1 n2 -> lookup (update c n1 a) n2 = lookup c n2.
Parameter indep_lookup_2 : forall c n1 n2 a x, ~Key.eq n1 n2 -> lookup (update c n1 a) n2 = Some x -> lookup c n2 = Some x.
Parameter remove_lookup : forall l k, lookup (remove k l) k = None.
Parameter remove_lookup_2 : forall l k1 k2, lookup l k1 = None -> lookup (remove k2 l) k1  = None.
Parameter remove_lookup_3 : forall k1 k2 c o, lookup (remove k1 c) k2 = Some o -> lookup c k2 = Some o.
Parameter remove_lookup_4 : forall c nm nm' x, lookup c nm = Some x -> ~Key.eq nm' nm -> lookup (remove nm' c) nm = Some x.

Definition eq_key_obj := fun x y : key * object => Key.eq (fst x) (fst y) /\ snd x = snd y.

Parameter elements_1 : forall s k o, lookup s k = Some o -> InA eq_key_obj (k,o) (elements s).
Parameter elements_2 : forall s k o, InA eq_key_obj (k,o) (elements s) -> lookup s k = Some o.
Parameter elements_empty : elements empty = nil.

Parameter lookup_eq : forall s k1 k2, Key.eq k1 k2 -> lookup s k1 = lookup s k2.

Parameter remove_by_lookup : forall l k f, (forall k k', Key.eq k k' -> f k = f k') -> f k = true -> lookup (remove_by f l) k = None.

(*Parameter commute_remove : forall s x y, remove x (remove y s) = remove y (remove x s).
Parameter remove_by_lookup : forall l k f, f k = true -> lookup (remove_by f l) k = None.
Hypothesis check_all_correct : forall s f (P:key->object->Prop),
  (forall k o, f k o = true -> P k o) ->
  check_all s f = true -> (forall k o, lookup s k = Some o -> P k o).*)

(* Recursion over removals *)
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

Parameter all_wf_removals : forall s, wf_removals s.

End STORE.
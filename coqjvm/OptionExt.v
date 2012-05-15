Lemma option_dec : forall A (x:option A), (exists a, x = Some a) \/ x = None.
intros. destruct x; [left;exists a|right];trivial.
Save.
Implicit Arguments option_dec [A].

Definition option_map : forall (A B:Type), (A->B) -> option A -> option B :=
  fun A B f oa => match oa with
  | None => None
  | Some a => Some (f a)
  end.
Implicit Arguments option_map [A B].

Inductive option_incl (A:Type) : option A -> option A -> Prop :=
| o_inc_1 : option_incl A None None
| o_inc_2 : forall a, option_incl A None (Some a)
| o_inc_3 : forall a, option_incl A (Some a) (Some a).
Implicit Arguments option_incl [A].

Lemma option_incl_refl : forall (A:Type) (o:option A), option_incl o o.
intros. destruct o. apply o_inc_3. apply o_inc_1.
Save.

Lemma option_incl_trans : forall (A:Type) (o1 o2 o3:option A), option_incl o1 o2 -> option_incl o2 o3 -> option_incl o1 o3.
intros. 
destruct H; inversion H0.
apply o_inc_1. apply o_inc_2. apply o_inc_2. apply o_inc_3.
Save.

Definition option_eq_dec : forall (A:Type) (A_eq_dec:forall (a b:A), {a=b}+{a<>b}) (o1 o2:option A), {o1=o2}+{o1<>o2}.
intros A A_eq_dec. decide equality. 
Defined.

Definition option_to_bool : forall A, option A -> bool :=
  fun A o => match o with
  | None => false
  | Some _ => true
  end.
Implicit Arguments option_to_bool [A].

Definition option_mult : forall A, option (option A) -> option A :=
  fun A o => match o with
  | None => None
  | Some f => f
  end.
Implicit Arguments option_mult [A].

Definition option_informative : forall (A:Type) (o:option A), {a:A | o = Some a} + {o = None}.
intros. destruct o. left. exists a. trivial. right. trivial. 
Defined.
Implicit Arguments option_informative [A].

Lemma Some_isnt_None : forall (A:Type) x (a:A),
  x = Some a -> x <> None.
unfold not. intros. subst. discriminate.
Save.
Implicit Arguments Some_isnt_None [A x a].

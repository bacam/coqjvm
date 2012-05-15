Require Import Relation_Definitions.
Require Import List.
Require Import OrderedType.
Require Import OrderedTypeEx.

Section RelationUtils.

Variable A : Type.

Variable R : relation A.

(* Lifting relations up to option types *)

Definition option_relation : relation (option A) :=
 fun x y => match x, y with
 | Some x, Some y => R x y
 | None,   None   => True
 | _,      _      => False
 end.

Lemma option_relation_reflexivity : reflexive _ R -> reflexive _ option_relation.
unfold reflexive. destruct x; simpl; auto.
Save.

Lemma option_relation_symmetry : symmetric _ R -> symmetric _ option_relation.
unfold symmetric. destruct x; destruct y; simpl in *; intuition.
Save.

Lemma option_relation_transitivity : transitive _ R -> transitive _ option_relation.
unfold transitive. destruct x; destruct y; destruct z; simpl in *; intuition eauto.
Save.

Lemma option_relation_antisymmetry : antisymmetric _ R -> antisymmetric _ option_relation.
unfold antisymmetric. destruct x; destruct y; simpl in *; intuition.
rewrite (H a a0); auto.
Save.

(* Lifting relations up to option types, without relating None *)

Variable R2 : relation A.

Hypothesis R_R2 : forall x y z, R x y -> R2 y z -> R2 x z.
Hypothesis R2_R : forall x y z, R x y -> R2 z y -> R2 z x.

Definition option_relation2 : relation (option A) :=
 fun x y => match x, y with
 | Some x, Some y => R2 x y
 | None,   Some _ => True
 | None,   None   => False
 | Some _, None   => False
 end.

Lemma option_relation2_transitivity : transitive _ R2 -> transitive _ option_relation2.
unfold transitive. destruct x; destruct y; destruct z; simpl in *; intuition eauto.
Save.

Lemma option_relation2_antisymmetry : antisymmetric _ R2 -> antisymmetric _ option_relation2.
unfold antisymmetric. destruct x; destruct y; simpl in *; intuition.
rewrite (H a a0); auto.
Save.

Lemma option_R2_not_R : (forall x y, R2 x y -> ~R x y) -> (forall x y, option_relation2 x y -> ~option_relation x y).
destruct x; destruct y; simpl; intuition eauto.
Save.

Lemma option_R_R2 : forall x y z, option_relation x y -> option_relation2 y z -> option_relation2 x z.
destruct x; destruct y; destruct z; simpl; intuition eauto.
Save.

Lemma option_R2_R : forall x y z, option_relation x y -> option_relation2 z y -> option_relation2 z x.
destruct x; destruct y; destruct z; simpl; intuition eauto.
Save.

Hint Constructors Compare.
Hint Unfold option_relation option_relation2.
Hint Resolve option_relation_reflexivity option_relation_symmetry option_relation_transitivity option_relation_antisymmetry
             option_relation2_transitivity option_relation2_antisymmetry.

Definition option_compare : (forall x y, Compare R2 R x y) -> (forall x y, Compare option_relation2 option_relation x y).
destruct x; destruct y; intuition eauto.
 destruct (X a a0); intuition eauto.
Defined.

(* Lifting relations up to lists *)

Fixpoint list_relation (l1:list A) (l2:list A) {struct l1} : Prop :=
 match l1, l2 with
 | nil,   nil   => True
 | a::l1, b::l2 => R a b /\ list_relation l1 l2
 | _,     _     => False
 end.

Lemma list_relation_reflexivity : reflexive _ R -> reflexive _ list_relation.
unfold reflexive. induction x; simpl in *; auto.
Save.

Lemma list_relation_symmetry : symmetric _ R -> symmetric _ list_relation.
unfold symmetric. induction x; destruct y; simpl in *; intuition.
Save.

Lemma list_relation_transitivity : transitive _ R -> transitive _ list_relation.
unfold transitive. induction x; destruct y; destruct z; simpl in *; intuition eauto.
Save.

Lemma list_relation_antisymmetry : antisymmetric _ R -> antisymmetric _ list_relation.
unfold antisymmetric. induction x; destruct y; simpl in *; intuition.
rewrite (H a a0); [|assumption|assumption].
rewrite (IHx y); [|assumption|assumption].
reflexivity.
Save.

(* Lifting relations up to lists, without relating the empty list *)

Fixpoint list_relation2 (l1:list A) (l2:list A) {struct l1} : Prop :=
 match l1, l2 with
 | nil,   nil   => False
 | nil,   _::_  => True
 | _::_,  nil   => False
 | a::l1, b::l2 => R2 a b \/ R a b /\ list_relation2 l1 l2
 end.

Lemma list_relation2_transitivity : symmetric _ R -> transitive _ R2 -> transitive _ R -> transitive _ list_relation2.
unfold transitive. induction x; destruct y; destruct z; simpl in *; intuition eauto.
Save.

Lemma list_R2_not_R : (forall x y, R2 x y -> ~R x y) -> (forall x y, list_relation2 x y -> ~list_relation x y).
induction x; destruct y; simpl; intuition eauto.
Save.

Hint Unfold list_relation list_relation2.
Hint Resolve list_relation_reflexivity list_relation_symmetry list_relation_transitivity list_relation_antisymmetry
             list_relation2_transitivity
             option_R2_not_R list_R2_not_R.

Hypothesis R_sym : symmetric _ R.
Hint Unfold symmetric.

Definition list_compare : (forall x y, Compare R2 R x y) -> (forall x y, Compare list_relation2 list_relation x y).
induction x; destruct y; intuition eauto.
destruct (X a a0); intuition eauto.
destruct (IHx y); intuition eauto 6.
Defined.

Lemma list_R_R2 : transitive _ R -> forall x y z, list_relation x y -> list_relation2 y z -> list_relation2 x z.
induction x; destruct y; destruct z; simpl; intuition eauto.
Save.

Lemma list_R2_R : transitive _ R -> forall x y z, list_relation x y -> list_relation2 z y -> list_relation2 z x.
induction x; destruct y; destruct z; simpl; intuition eauto.
Save.

Hint Resolve option_R_R2 option_R2_R list_R_R2 list_R2_R.

End RelationUtils.

Module OptionMiniOrderedType (O : MiniOrderedType)
                       <: MiniOrderedType.

Definition t := option O.t.

Definition eq := option_relation O.t O.eq.

Definition lt := option_relation2 O.t O.lt.

Hint Unfold eq lt reflexive symmetric transitive.

Lemma eq_refl : forall x, eq x x.
intros. apply (option_relation_reflexivity O.t O.eq). auto.
Save.

Lemma eq_sym : forall x y, eq x y -> eq y x.
intros. apply (option_relation_symmetry O.t O.eq); auto.
Save.

Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
intros. refine (option_relation_transitivity O.t O.eq _ _ _ _ _ _); eauto.
Save.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
intros. refine (option_relation2_transitivity O.t O.lt _ _ _ _ _ _); eauto.
Save.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
intros. unfold eq. eapply option_R2_not_R. apply O.lt_not_eq. apply H.
Save.

Definition compare : forall x y, Compare lt eq x y.
unfold eq. unfold lt.
intros. eapply option_compare. apply O.compare.
Defined.

End OptionMiniOrderedType.

Module OptionOrderedType (O : MiniOrderedType)
                       <: OrderedType.

Module MOT := OptionMiniOrderedType(O).
Module OT := MOT_to_OT(MOT).
Include OT.

End OptionOrderedType.

Module OptionUsualOrderedType (U : UsualOrderedType) <: UsualOrderedType.

Definition t := option U.t.

Definition eq := @eq (option U.t).
Definition eq_refl  := @refl_equal t.
Definition eq_sym   := @sym_eq t.
Definition eq_trans := @trans_eq t.

Definition lt := option_relation2 U.t U.lt.

Hint Resolve U.lt_trans U.lt_not_eq f_equal.
Hint Unfold transitive symmetric reflexive U.eq eq.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
intros. refine (option_relation2_transitivity U.t U.lt _ _ _ _ _ _); eauto.
Save.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
destruct x; destruct y; unfold eq; simpl; intuition first [congruence|eauto].
 inversion H0. apply (U.lt_not_eq _ _ H H2).
Save.

Hint Constructors Compare.
Hint Unfold option_relation2.

Lemma compare : forall x y, Compare lt eq x y.
unfold lt. unfold eq.
intros. destruct x; destruct y; intuition eauto.
 destruct (U.compare t0 t1); intuition eauto.
Defined.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.
  intros; elim (compare x y); intro H; [ right | left | right ]; auto using lt_not_eq.
  assert (~ eq y x); auto using lt_not_eq.
Defined.


End OptionUsualOrderedType.

Module ListOrderedType (O : OrderedType) <: OrderedType.

Module OFacts := OrderedTypeFacts O.

Definition t := list O.t.

Definition eq := list_relation O.t O.eq.

Definition lt := list_relation2 O.t O.eq O.lt.

Hint Unfold eq lt reflexive symmetric transitive.

Lemma eq_refl : forall x, eq x x.
intros. apply (list_relation_reflexivity O.t O.eq). auto.
Save.

Lemma eq_sym : forall x y, eq x y -> eq y x.
intros. apply (list_relation_symmetry O.t O.eq); auto.
Save.

Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
intros. refine (list_relation_transitivity O.t O.eq _ _ _ _ _ _); eauto.
Save.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
intros. refine (list_relation2_transitivity O.t O.eq _ _ _ _ _ _ _ _ _ _ _); eauto.
 intros. eapply OFacts.lt_eq; eauto.
Save.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
intros. unfold eq. eapply list_R2_not_R. apply O.lt_not_eq. apply H.
Save.

Definition compare : forall x y, Compare lt eq x y.
unfold eq. unfold lt.
intros. eapply list_compare. auto. apply O.compare.
Defined.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.
  intros; elim (compare x y); intro H; [ right | left | right ]; auto using lt_not_eq.
  assert (~ eq y x); auto using lt_not_eq, eq_sym.
Defined.

End ListOrderedType.

Module ListUsualOrderedType (U : UsualOrderedType) <: UsualOrderedType.

Definition t := list U.t.

Definition eq := @eq t.
Definition eq_refl  := @refl_equal t.
Definition eq_sym   := @sym_eq t.
Definition eq_trans := @trans_eq t.

Definition lt := list_relation2 U.t U.eq U.lt.

Hint Resolve U.lt_trans U.lt_not_eq eq_trans U.eq_trans.
Hint Unfold transitive symmetric reflexive U.eq eq.
Hint Immediate U.eq_sym.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
intros. refine (list_relation2_transitivity U.t U.eq _ _ _ _ _ _ _ _ _ _ _); eauto;
 unfold U.eq; intros; subst; assumption.
Save.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
induction x; destruct y; unfold eq; simpl; intuition first [congruence|eauto].
 inversion H0. apply (U.lt_not_eq _ _ H1 H2).
 inversion H0. eauto.
Save.

Hint Constructors Compare.
Hint Unfold list_relation2.

Lemma compare : forall x y, Compare lt eq x y.
unfold lt. unfold eq.
induction x; destruct y; intuition eauto.
 destruct (U.compare a t0); intuition eauto.
  destruct (IHx y); intuition eauto.
   apply EQ. unfold U.eq in e. subst. reflexivity.
   apply GT. unfold list_relation2. right. split; auto.
Defined.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.
  intros; elim (compare x y); intro H; [ right | left | right ]; auto using lt_not_eq.
  assert (~ eq y x); auto using lt_not_eq, eq_sym.
Defined.

End ListUsualOrderedType.


Module PairUsualOrderedType (U1 : UsualOrderedType) (U2 : UsualOrderedType) <: UsualOrderedType.

Definition t := (U1.t * U2.t)%type.

Definition eq := @eq t.
Definition eq_refl  := @refl_equal t.
Definition eq_sym   := @sym_eq t.
Definition eq_trans := @trans_eq t.

Definition lt (a b:t) := let (a1,a2) := a in let (b1,b2) := b in U1.lt a1 b1 \/ a1 = b1 /\ U2.lt a2 b2.

Hint Resolve U1.lt_trans U2.lt_trans U1.lt_not_eq U2.lt_not_eq U1.eq_refl.
Hint Unfold not eq.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
unfold lt. destruct x. destruct y. destruct z. intuition; subst; eauto.
Save.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
unfold lt. unfold eq. destruct x. destruct y.
intuition.
 inversion H0. apply (U1.lt_not_eq _ _ H1). assumption.
 inversion H0. apply (U2.lt_not_eq _ _ H2 H4).
Save.

Lemma compare : forall x y, Compare lt eq x y.
unfold lt. unfold eq. destruct x. destruct y.
destruct (U1.compare t0 t2).
 apply LT. auto.
 destruct (U2.compare t1 t3).
  apply LT. auto.
  apply EQ. unfold U1.eq in e. unfold U2.eq in e0. subst. reflexivity.
  apply GT. auto.
 apply GT. auto.
Defined.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof.
  intros; elim (compare x y); intro H; [ right | left | right ]; auto using lt_not_eq.
  assert (~ eq y x); auto using lt_not_eq, eq_sym.
Defined.

End PairUsualOrderedType.












Require Import List.
Require Import Arith.
Require Omega.
Require Import OptionExt.

Lemma list_dec : forall A (l:list A), (exists h, exists t, l = h::t) \/ l = nil.
intros. destruct l;[right; trivial| left; exists a; exists l]; trivial.
Save.

Lemma nth_error_ok : forall (A:Type) (l:list A) n, n < length l -> exists x, nth_error l n = Some x.
intros A l. induction l; intros.
elimtype False. generalize H. apply lt_n_O. 
destruct (O_or_S n). 
destruct s. subst n. simpl. apply IHl. simpl in H. apply lt_S_n. apply H.
subst n. simpl. exists a. trivial.
Save.

Lemma nth_error_length_2 : forall (A:Type) (l:list A) n x, nth_error l n = Some x -> n < length l.
intros. generalize l H. clear l H.
induction n; intros; destruct l; try discriminate; simpl.
auto with arith.
simpl in H. auto with arith. 
Save.

Fixpoint tail (A:Type) (n:nat) (ops:list A) {struct n} : list A :=
  match n, ops with
  | 0, ops => ops
  | S n, _::ops => tail A n ops
  | S n, nil => nil
  end.
Implicit Arguments tail [A].

Lemma nth_error_tail : forall (A:Type) n (l l':list A) o, tail n l = o::l' -> nth_error l n = Some o.
intros A n.
induction n; intros; destruct l; try discriminate.
inversion H. subst o. trivial.
simpl in * |- *. eapply IHn. apply H.
Save.

Lemma tail_nth_error : forall (A:Type) n (l:list A) o, nth_error l n = Some o -> exists l', tail n l = o::l'.
intros A n.
induction n; intros; destruct l; try discriminate.
inversion H. subst o. exists l. trivial.
simpl in * |- *. apply IHn. apply H.
Save.
Implicit Arguments tail_nth_error [A].

Lemma tail_0 : forall (A:Type) (l:list A), tail 0 l = l.
trivial.
Save.
Implicit Arguments tail_0 [A].

Lemma tail_S : forall (A:Type) n (l:list A), n < length l -> exists a, tail n l = a :: tail (S n) l.
intros A n. induction n; intros.
destruct l. elimtype False. apply (lt_n_O 0 H).
simpl. exists a. trivial.
destruct l. elimtype False. apply (lt_n_O (S n) H).
simpl in H. assert (n < length l). auto with arith.
destruct (IHn l H0).
exists x. simpl. apply H1.
Save.
Implicit Arguments tail_S [A].

Lemma tail_minus : forall (A:Type) (l:list A) n' n, n' < n -> n < length l -> exists a, tail (n - S n') l = a::tail (n-n') l.
intros. replace (n-n') with (S (n - S n')).
apply tail_S. omega. omega.
Save.
Implicit Arguments tail_minus [A].

Lemma app_length : forall A (l1 l2:list A), length (l1 ++ l2) = length l1 + length l2.
intros. induction l1. trivial. simpl. rewrite IHl1. trivial.
Save.

Lemma rev_length : forall A (l:list A), length (rev l) = length l.
intros. induction l. trivial. simpl. rewrite app_length. rewrite IHl. simpl. omega.
Save.

Lemma map_length : forall (A B:Type) (l:list A) (f:A->B), length (map f l) = length l. 
intros. induction l. trivial. simpl. rewrite IHl. trivial. 
Save.

Lemma map_app : forall (A B:Type) (l1 l2:list A) (f:A->B), map f (l1 ++ l2) = map f l1 ++ map f l2.
intros. induction l1. trivial. simpl. rewrite IHl1. trivial.
Save.

Lemma map_rev : forall (A B:Type) (l:list A) (f:A->B), map f (rev l) = rev (map f l).
intros. induction l. trivial.
simpl. rewrite map_app. rewrite IHl. trivial.
Save.

Fixpoint list_update (A:Type) (l:list A) (n:nat) (v:A) {struct n} : option (list A) :=
  match n, l with
  | 0,   old_v::rest => Some (v::rest)
  | S n, v'::rest    => match list_update A rest n v with None => None | Some rest' => Some (v'::rest') end
  | _,   nil         => None
  end.
Implicit Arguments list_update [A].

Lemma list_update_nth_error : forall (A:Type) (l l':list A) n x,
  list_update l n x = Some l' -> nth_error l' n = Some x.
intros. generalize l l' H. clear l l' H. 
induction n; intros; destruct l; inversion H.
 trivial.
 destruct (option_dec (list_update l n x)) as [[x' update_res]|update_res]; rewrite update_res in H1.
  inversion H1. simpl. eauto.
  discriminate.
Save.

Lemma list_update_length : forall (A:Type) (l l':list A) n v,
  list_update l n v = Some l' -> length l = length l'.
intros A l. 
induction l; intros; destruct n; destruct l'; try discriminate; simpl in * |- *.
inversion H. trivial. 
destruct (list_update l n v); discriminate.
destruct (option_dec (list_update l n v)) as [[x' update_res]|update_res]; rewrite update_res in H.
 inversion H. subst. rewrite (IHl _ _ _ update_res). reflexivity.
 discriminate.
Save.

Lemma list_update_lt_length : forall (A:Type) (l:list A) v n,
  n < length l -> exists l', list_update l n v = Some l'.
intros A l v. 
induction l; intros; destruct n.
elimtype False. apply (lt_n_O _ H). 
elimtype False. apply (lt_n_O _ H). 
exists (v::l). trivial.
simpl in * |- *. destruct (IHl _ (lt_S_n _ _ H)). rewrite H0. exists (a::x). trivial.
Save.

Lemma list_update_lt_length_2 : forall (A:Type) (l l':list A) v n,
 list_update l n v = Some l' -> n < length l'.
intros A l.
induction l; intros; destruct n.
inversion H. 
inversion H. 
inversion H. simpl. auto with arith. 
simpl in H. destruct (option_dec (list_update l n v)) as [[x' update_res]|update_res]; rewrite update_res in H.
 inversion H. simpl. eauto using lt_n_S.
 discriminate.
Save.

Lemma nth_error_length : forall A (l:list A) v n,
 nth_error l n = Some v -> n < length l.
intros A l v.
induction l; intros; destruct n; try discriminate; simpl in * |- *.
auto with arith. 
apply lt_n_S. auto. 
Save.

Lemma list_update_indep : forall (A:Type) (l l':list A) n n' v x,
  nth_error l n = Some x -> list_update l n' v = Some l' -> n <> n' ->
  nth_error l' n = Some x.
intros A l.
induction l; intros; destruct n; try discriminate.
 inversion H. subst. destruct n'. 
  elimtype False. apply H1. trivial. 
  simpl in H0. destruct (list_update l n' v); try discriminate.
  inversion H0. subst. trivial.
 simpl in H. destruct n'. 
  inversion H0. simpl. assumption.
  simpl in H0. destruct (option_dec (list_update l n' v)) as [[x' update_res]|update_res]; rewrite update_res in H0.
   inversion H0. subst. simpl. intuition first[eauto|omega].
   discriminate.  
Save.

Lemma is_nil : forall A (x:list A), {x=nil}+{x<>nil}.
intros. destruct x; [left;trivial|right; unfold not; intro; discriminate].
Save.
Implicit Arguments is_nil [A].

Definition list_informative : forall (A:Type) (l:list A), { a : A & { l' : list A | l = a::l' } }+{l = nil}.
intros. destruct l.
 right. reflexivity.
 left. exists a. exists l. reflexivity.
Defined.
Implicit Arguments list_informative [A].

Section holds_for_list.

Hypothesis A: Type.
Hypothesis P:A->Prop.

Inductive holds_for_list : list A -> Prop :=
| holds_for_nil : holds_for_list nil
| holds_for_cons : forall a t, P a -> holds_for_list t -> holds_for_list (a::t).

End holds_for_list.

Implicit Arguments holds_for_list [A].

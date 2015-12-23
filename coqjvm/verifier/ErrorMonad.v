(** * Monad for error reporting *)

Require Import MLStrings.
Require List.

(** Errors are represented by strings. *)

Definition error := MLString.

Inductive error_monad (T:Type) : Type :=
| Val : T -> error_monad T
| Err : error -> error_monad T.

Definition ret (T:Type) (t:T) := Val T t.
Definition bind (T T':Type) (t1:error_monad T) (t2:T->error_monad T') :=
  match t1 with
    | Val _ v => t2 v
    | Err _ e => Err T' e
  end.
Definition fail (T:Type) (s:error) := Err T s.

(** ** Adding extra context information to an error. *)

Definition tagfailure (T:Type) (s:error) (t:error_monad T) :=
  match t with
    | (Val _ _) as v => v
    | Err _ e => Err T (s mlapp e)
  end.

(** ** Translating booleans and options to errors. *)

Definition tagboolfail (s:error) (t:bool) :=
  if t then Val unit tt else Err unit s.

Definition tagoptfail (T:Type) (s:error) (t:option T) :=
  match t with
    | Some v => Val T v
    | None => Err T s
  end.

Definition opterror (t:option error) : error_monad unit :=
  match t with
    | None => Val unit tt
    | Some e => Err unit e
  end.

Implicit Arguments Val [T].
Implicit Arguments Err [T].
Implicit Arguments ret [T].
Implicit Arguments bind [T T'].
Implicit Arguments fail [T].
Implicit Arguments tagfailure [T].
Implicit Arguments tagoptfail [T].

(** ** More readable notation *)

Notation "t1 ;; t2" := (bind t1 (fun _ => t2)) (at level 20, right associativity).
Notation "x <- t1 ;: t2" := (bind t1 (fun x => t2)) (at level 20, right associativity).
(* Inline versions -- useful for coq's Program stuff. *)
Notation "t1 ;;; t2" := (match t1 with Val _ => t2 | Err e => Err e end) (at level 20, right associativity).
Notation "x <- t1 ;:: t2" := (match t1 with Val x => t2 | Err e => Err e end) (at level 20, right associativity).

(** ** Tactics for destruction of monad values *)

Ltac destruct_err t t' result resulteq :=
  case_eq t; intros result resulteq;
  rewrite resulteq in t';
  [simpl in t'|discriminate].

Ltac inject_err t :=
  unfold ret in t; injection t; clear t; intro t.

Ltac inject_opttag H :=
  let v := fresh "v" in
  let veq := fresh "veq" in
  let veq' := fresh "veq'" in
  match type of H with tagoptfail _ ?t = Val _ =>
    case_eq t; [intros v veq|intro veq]; rewrite veq in H;
    [simpl in H| discriminate];
    injection H; intro veq'; rewrite veq' in * |- *;
    clear H veq' v; rename veq into H
  end.

Ltac inject_booltag H :=
  let veq := fresh "veq" in
  match type of H with tagboolfail _ ?t = Val _ =>
    case_eq t; intro veq; rewrite veq in H;
    [simpl in H| discriminate];
    clear H; rename veq into H
  end.

Ltac destruct_opttag H res reseq :=
  match type of H with bind ?t _ = Val _ =>
    destruct_err t H res reseq; inject_opttag reseq
  end.

(** ** List operations *)
(** Applying a test to each element of a list. *)

Definition check_list (X:Type) (f:X -> error_monad unit) (l:List.list X) : error_monad unit :=
  List.fold_left (fun e x => @bind unit unit e (fun _ => f x)) l (@Val unit tt).

Lemma check_list_ok : forall X f l v,
  check_list X f l = @Val unit tt -> List.In v l -> f v = @Val unit tt.
Proof.
  intros.
  unfold check_list in H.
  induction l.
    inversion H0.

    inversion H0.
      subst a.
      simpl in H.
      destruct (f v).
        destruct u.
        reflexivity.
        
        clear IHl H0.
        induction l.
          discriminate.

          apply IHl.
          assumption.

      simpl in H.
      destruct (f a).
        destruct u.
        apply IHl; assumption.

        clear IHl H0 H1.
        induction l.
          discriminate.

          apply IHl; assumption.
Qed.

Implicit Arguments check_list [X].
Implicit Arguments check_list_ok [X f l v].

(** A version of list filter which handles errors. *)

Fixpoint filter_list (X:Type) (f:X -> error_monad bool) (l:List.list X) : error_monad (List.list X) :=
  match l with
    | List.nil => ret List.nil
    | List.cons h t => b <- f h;: t' <- filter_list X f t;: ret (if b then List.cons h t' else t')
  end.

Lemma filter_list_In : forall X f l' l x,
  filter_list X f l = Val l' ->
  List.In x l' ->
  f x = Val true.
Proof.
  induction l'.
    contradiction.

    intros.
    inversion H0.
      subst a.
      induction l.
        inversion H.

        simpl in H.
        destruct_err (f a) H b beq.
        destruct_err (filter_list X f l) H t' t'eq.
        inject_err H.
        destruct b.
          inversion H.
          subst a.
          assumption.

          apply IHl.
          rewrite <- H.
          assumption.

    induction l.
      inversion H.

      simpl in H.
      destruct_err (f a0) H b beq.
      destruct_err (filter_list X f l) H t' t'eq.
      inject_err H.
      destruct b.
        inversion H.
        subst a0 t'.
        eapply IHl'.
          eassumption.
          apply H1.

        apply IHl.
        rewrite <- H.
        assumption.
Qed.

Lemma filter_list_out : forall X f l l' x,
  filter_list X f l = Val l' ->
  List.In x l ->
  ~ List.In x l' ->
  f x = Val false.
Proof.
  induction l; intros; inversion H0.
    subst a.
    simpl in H.
    destruct_err (f x) H b beq.
    destruct_err (filter_list X f l) H t' t'eq.
    inject_err H.
    destruct b.
      rewrite <- H in H1.
      destruct H1.
      left.
      reflexivity.

      reflexivity.

    simpl in H.
    destruct_err (f a) H b beq.
    destruct_err (filter_list X f l) H t' t'eq.
    inject_err H.
    destruct b.
      eapply IHl; eauto.
      intro int'.
      apply H1.
      rewrite <- H.
      right.
      assumption.

      subst t'.
      eapply IHl; eauto.
Qed.      

(** ** Apply a function to each element of a list and combine the results *)

Section CombiningFold.

Variable t:Type.
Hypothesis t_ok : t -> Prop.
Variable t_comb : t -> t -> t.
Hypothesis t_comb_1 : forall t1 t2, t_ok (t_comb t1 t2) -> t_ok t1.
Hypothesis t_comb_2 : forall t1 t2, t_ok (t_comb t1 t2) -> t_ok t2.

Definition fold_err (B:Type) (f : B -> error_monad t) (l:List.list B) (a:t) :=
  List.fold_left (fun a b => a' <- a;: a'' <- f b;: ret (t_comb a' a'')) l (ret a).

Lemma fold_err_ok : forall B f l a r x,
  fold_err B f l a = Val r ->
  t_ok r ->
  List.In x l ->
  exists t, f x = Val t /\ t_ok t.
Proof.
  unfold fold_err.
  induction l; intros; inversion H1.
    subst a.
    simpl in H.
    destruct (f x).
      exists t0. split; auto.
      simpl in H.
      apply t_comb_2 with (t1:=a0).
      set (t0' := t_comb a0 t0) in *.
      generalize t0' H.
      clear - H0 t_comb_1.
      induction l; simpl; intros.
        injection H as Heq. subst r. auto.
        destruct (f a).
          simpl in *. apply t_comb_1 with (t2:=t0). apply IHl. assumption.
          simpl in H. elimtype False. clear - H. induction l.
            discriminate.
            eapply IHl; eauto.
      simpl in H. elimtype False. clear - H. induction l.
        discriminate.
        eapply IHl; eauto.
    simpl in H.
    destruct (f a).
      simpl in H.
      eapply IHl; eauto.

      simpl in H. elimtype False. clear - H. induction l.
        discriminate.
        eapply IHl; eauto.
Qed.

End CombiningFold.

Implicit Arguments filter_list [X].
Implicit Arguments filter_list_In [X].
Implicit Arguments filter_list_out [X].


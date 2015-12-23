Require Import ILLInterfaces.
Require Import ILLSimplifierIface.
Require Import List.
Require Import FSetProperties.
Require Setoid.
Require Import Omega.

Require Import BasicMachineTypes.

(* This module performs formulae simplification by eliminating some
   trivally true subformulae.  You could add more simplification, but this
   is more than enough to make the ILL VCs bearable. *)

Module ILLSimplifier
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B)
  (SYN : ILL_SYNTAX B BASESYN) : ILL_SIMPLIFIER B BASESYN SYN.

Import BASESYN.

Fixpoint simplify (f : formula) :=
  match f with
    | f_tensor f1 f2 =>
        match (simplify f1, simplify f2) with
          | (f_i, f2) => f2
          | (f1, f_i) => f1
          | (f1,f2) => f_tensor f1 f2
        end
    | f_and f1 f2 =>
        match (simplify f1, simplify f2) with
          | (f_i, f2) => f2
          | (f1, f_i) => f1
          | (f1,f2) =>
            if formula_eq_dec f1 f2 then f1 else f_and f1 f2
        end
    | f_lolli f1 f2 =>
        match (simplify f1, simplify f2) with
          | (f_i, f2) => f2
          | (_,  f_i) => f_i
          | (f1,  f2) =>
            if formula_eq_dec f1 f2 then f_i else f_lolli f1 f2
        end
    | f => f
  end.

Import SYN.

Theorem simplify_ok : forall f, implies f (simplify f) /\ implies (simplify f) f.
Proof.

Ltac tensor_breakup f var prf :=
  destruct prf as [prf_t [prf_U prf]];
  apply implies_trans with (B:=f); unfold implies; do 2 eexists;
     [ eapply prf_tensor_elim;
       [ apply prf_lvar with (n:=0); simpl; reflexivity; apply VarSet.eq_refl
       | apply prf_lvar with (n:=var); simpl; reflexivity; apply VarSet.eq_refl
       | (intros x xin; pose (xin' := VarSet.inter_1 xin); apply VarSet.singleton_1 in xin'; unfold VarSet.E.eq in xin'; subst x;
          apply VarSet.inter_2 in xin; do 2 apply shift_down_In in xin; apply VarSet.singleton_1 in xin; unfold VarSet.E.eq in xin;
          discriminate)
       | reflexivity]
     | apply prf].

Ltac simplify_result f :=
  let rem := fresh "rem" in
  match goal with |- context [prf nil _ _ ?X _] => set (rem := X) end;
  assert (rem = simplify f) by (destruct (simplify f); tauto);
  clearbody rem;
  subst rem.

Ltac simplify_result2 f1 f2 fop :=
  let rem := fresh "rem" in
  match goal with |- context [prf nil _ _ ?X _] => set (rem := X) end;
  assert (rem = fop (simplify f1) (simplify f2)) by (destruct (simplify f1); destruct (simplify f2); tauto);
  clearbody rem;
  subst rem.

Ltac simplify_ctx f :=
  let rem := fresh "rem" in
  match goal with |- context [prf nil (?X::nil) _ _ _] => set (rem := X) end;
  assert (rem = simplify f) by (destruct (simplify f); auto);
  clearbody rem;
  subst rem.

Ltac simplify_ctx2 f1 f2 fop :=
  let rem := fresh "rem" in
  match goal with |- context [prf nil (?X::nil) _ _  _] => set (rem := X) end;
  assert (rem = fop (simplify f1) (simplify f2)) by (destruct (simplify f1); destruct (simplify f2); tauto);
  clearbody rem;
  subst rem.

Ltac tensor_create f1 f2 prf prf' :=
  destruct prf as [prf_t [prf_U prf]];
  destruct prf' as [prf_t' [prf_U' prf']];
  apply implies_trans with (B:=(f_tensor f1 f2));
  [ unfold implies; do 2 eexists; eapply prf_tensor_intro;
    first [ apply prf_lvar with (n:=0); reflexivity
          | apply prf_i_intro; reflexivity
          | intros x xin; apply VarSet.inter_1 in xin; apply (VarSet.empty_1 xin)
          | intros x xin; apply VarSet.inter_2 in xin; apply (VarSet.empty_1 xin)
(* Workaround for https://logical.futurs.inria.fr/coq-bugs/show_bug.cgi?id=1971 *)
          | match goal with |- context [SYN.VarSet.Equal _ _] => reflexivity end
          ]
  | eapply implies_subformulae; try (unfold implies; do 2 eexists); eauto].



  induction f; simpl; auto; split;
  try destruct IHf as [IHf1 IHf1']; try destruct IHf1 as [IHf1 IHf1']; try destruct IHf2 as [IHf2 IHf2'];
  try (apply implies_refl) ;
  (compare (simplify f1) f_i; [intro s1; rewrite s1 in * | intro n1 |apply atom_eq_dec]); (compare (simplify f2) f_i; [intro s2; rewrite s2 in * | intro n2 |apply atom_eq_dec]); unfold implies;
  try solve
  [ unfold implies; do 2 eexists; apply prf_i_intro; apply VarSet.eq_refl
  | tensor_breakup f2 1 IHf2
  | simplify_result f1; tensor_breakup f1 0 IHf1
  | simplify_result2 f1 f2 f_tensor; apply implies_subformulae; auto
  | apply implies_trans with (B:=(f_tensor f_i f_i));
    [ unfold implies; do 2 eexists; eapply prf_tensor_intro; 
      first [apply prf_i_intro; reflexivity
            | intros x xin; apply VarSet.inter_1 in xin; apply (VarSet.empty_1 xin); reflexivity 
            | reflexivity]
    | eapply implies_subformulae; auto
    ]
  | tensor_create f_i (simplify f2) IHf1' IHf2'
  | simplify_ctx f1; tensor_create (simplify f1) f_i IHf1' IHf2'
  | simplify_ctx2 f1 f2 f_tensor; apply implies_subformulae; unfold implies; eauto
].

apply implies_trans with (B:=f_and f1 (simplify f2)).
apply implies_subformulae; unfold implies; eauto. do 2 eexists. apply prf_lvar with (n:=0); reflexivity.
unfold implies. do 2 eexists. apply prf_and_elim2 with (A:=f1). eapply prf_lvar with (n:=0); reflexivity.

simplify_result f1.
apply implies_trans with (B:=f_and (simplify f1) f2).
apply implies_subformulae; unfold implies; eauto. do 2 eexists. apply prf_lvar with (n:=0); reflexivity.
unfold implies. do 2 eexists. apply prf_and_elim1 with (B:=f2). eapply prf_lvar with (n:=0); reflexivity.

destruct (formula_eq_dec (simplify f1) (simplify f2)).
  match goal with |- context [prf nil _ _ ?X _] => replace X with (simplify f1) end.
   apply implies_trans with (B:=f_and (simplify f1) (simplify f2)).
   apply implies_subformulae; unfold implies; eauto.
   do 2 eexists. eapply prf_and_elim1. apply prf_lvar with (n:=0); reflexivity.

   destruct (simplify f1); destruct (simplify f2); intuition.

  simplify_result2 f1 f2 f_and.  apply implies_subformulae; unfold implies; eauto.

apply implies_trans with (B:=f_and f_i f_i).
unfold implies; do 2 eexists. eapply prf_and_intro. apply prf_i_intro; reflexivity.  apply prf_i_intro; reflexivity. reflexivity.
apply implies_subformulae; unfold implies; eauto.

apply implies_trans with (B:=f_and f_i (simplify f2)).
unfold implies. do 2 eexists. eapply prf_and_intro. apply prf_i_intro;reflexivity. apply prf_lvar with (n:=0); reflexivity. reflexivity.
apply implies_subformulae; unfold implies; eauto. 

simplify_ctx f1.
apply implies_trans with (B:=f_and (simplify f1) f_i).
unfold implies. do 2 eexists. eapply prf_and_intro. apply prf_lvar with (n:=0); reflexivity. apply prf_i_intro;reflexivity. reflexivity.
apply implies_subformulae; unfold implies; eauto. 

destruct (formula_eq_dec (simplify f1) (simplify f2)).
  match goal with |- context [prf nil (?X::nil) _ _ _] => replace X with (simplify f1) end.
   apply implies_trans with (B:=f_and (simplify f1) (simplify f2)).
   do 2 eexists. eapply prf_and_intro.
    apply prf_lvar with (n:=0); reflexivity.
    rewrite e. apply prf_lvar with (n:=0); reflexivity.
    reflexivity.
   apply implies_subformulae; unfold implies; eauto.

   destruct (simplify f1); destruct (simplify f2); intuition.

 simplify_ctx2 f1 f2 f_and.
 apply implies_subformulae; unfold implies; eauto.

apply implies_trans with (B:=f2).
destruct IHf1' as [t1' [U1' p1']]. 
unfold implies. do 2 eexists.  eapply prf_lolli_elim. apply prf_lvar with (n:=0); simpl; reflexivity.
eapply prf_let. apply prf_i_intro. reflexivity.
change (f_i::f_lolli f1 f2 :: nil) with ((f_i::nil)++(f_lolli f1 f2::nil)).
apply proof_weakening. apply p1'.
reflexivity. intros x xin. apply VarSet.inter_1 in xin. apply (VarSet.empty_1 xin).
reflexivity. intros x xin.
apply prf_uses_ctx with (n:=S x) in p1'. simpl in p1'. apply Lt.lt_S_n in p1'. apply (Lt.lt_n_O _ p1').
apply shift_down_In. apply VarSet.inter_2 in xin. destruct (VarSet.union_1 xin).
destruct (VarSet.empty_1 H). assumption. reflexivity.
assumption.

destruct (simplify f1); do 2 eexists; apply prf_i_intro; reflexivity.

destruct (formula_eq_dec (simplify f1) (simplify f2)).
 match goal with |- context [prf nil _ _ ?X _] => replace X with f_i end.
  do 2 eexists. apply prf_i_intro. reflexivity.
  destruct (simplify f1); destruct (simplify f2); tauto.

 simplify_result2 f1 f2 f_lolli.
 destruct IHf1' as [t1 [U1 p1]]. destruct IHf2 as [t2 [U2 p2]].
 do 2 eexists. eapply prf_lolli_intro. eapply prf_let.
 change (simplify f1 :: f_lolli f1 f2 :: nil) with ((simplify f1::nil)++(f_lolli f1 f2 :: nil)).
 apply proof_weakening. apply p1.
 eapply prf_let. eapply prf_lolli_elim. apply prf_lvar with (n:=2). simpl. reflexivity. reflexivity.
 apply prf_lvar with (n:=0). simpl. reflexivity. reflexivity.
 intros x xin.  pose (xin':=VarSet.inter_1 xin). clearbody xin'. apply VarSet.inter_2 in xin.
 apply VarSet.singleton_1 in xin. apply VarSet.singleton_1 in xin'. rewrite <- xin' in xin. discriminate.
 reflexivity.
 change (f2 :: f1 :: simplify f1 :: f_lolli f1 f2 :: nil) with ((f2::nil)++(f1 :: simplify f1 :: f_lolli f1 f2 :: nil)).
 apply proof_weakening. apply p2. reflexivity.
 intros x xin. apply VarSet.inter_2 in xin.
 apply prf_uses_ctx with (n:=S x) in p2. simpl in p2.  omega.
 apply shift_down_In. assumption.
 reflexivity. reflexivity.
 intros x xin. apply prf_uses_ctx with (n:=x) in p1. simpl in p1.
 apply VarSet.inter_2 in xin. apply shift_down_In in xin.
 destruct (VarSet.union_1 xin). destruct (VarSet.union_1 H).
 apply VarSet.singleton_1 in H0. unfold VarSet.E.eq in H0. omega.
 apply VarSet.singleton_1 in H0. unfold VarSet.E.eq in H0. omega.
 apply prf_uses_ctx with (n:=S (S x)) in p2. simpl in p2. omega.
 apply shift_down_In. assumption.
 apply VarSet.inter_1 in xin. assumption.
 reflexivity. reflexivity.

apply implies_trans with (B:=f2). assumption.
unfold implies. do 2 eexists. eapply prf_lolli_intro. apply prf_lvar with (n:=1). reflexivity. reflexivity. reflexivity.

apply implies_trans with (B:=f2). assumption.
unfold implies. do 2 eexists. eapply prf_lolli_intro. apply prf_lvar with (n:=1). reflexivity. reflexivity. reflexivity.

apply implies_trans with (B:=f2). destruct (simplify f1); assumption.
unfold implies. do 2 eexists. eapply prf_lolli_intro. apply prf_lvar with (n:=1). reflexivity. reflexivity. reflexivity.

destruct IHf1 as [t1 [U1 p1]]. destruct IHf2' as [t2 [U2 p2]].
destruct (formula_eq_dec (simplify f1) (simplify f2)).
 match goal with |- context [prf nil (?X::nil) _ _ _] => replace X with f_i end.
 do 2 eexists. eapply prf_lolli_intro.
 eapply prf_let.
  change (f1::f_i::nil) with ((f1::nil)++(f_i::nil)).
  apply proof_weakening. apply p1.

  rewrite e. change (simplify f2::f1::f_i::nil) with ((simplify f2::nil)++(f1::f_i::nil)).
  apply proof_weakening. apply p2.

  reflexivity.

  intros x xin. apply prf_uses_ctx with (n:=S x) in p2. simpl in p2. omega. 
  apply VarSet.inter_2 in xin. apply shift_down_In. assumption.
  reflexivity.
  reflexivity.

  destruct (simplify f1); destruct (simplify f2); tauto.

  match goal with |- context [prf _ (?R::nil) _ _ _] => set (r:=R) end.
  assert (r=f_lolli (simplify f1) (simplify f2)).
  destruct (simplify f1); try (destruct n1; reflexivity); destruct (simplify f2); try (destruct n2; reflexivity); simpl; reflexivity. 
  clearbody r.
 do 2 eexists.  eapply prf_lolli_intro.
 eapply prf_let.
   change (f1::r::nil) with ((f1::nil)++(r::nil)).
  apply proof_weakening. apply p1.
 eapply prf_let.
  eapply prf_lolli_elim.
   apply prf_lvar with (n:=2). simpl. subst r. reflexivity.
 reflexivity.
  apply prf_lvar with (n:=0). simpl. reflexivity. reflexivity.
 intros x xin.  pose (xin':=VarSet.inter_1 xin). clearbody xin'. apply VarSet.inter_2 in xin.
 apply VarSet.singleton_1 in xin. apply VarSet.singleton_1 in xin'. rewrite <- xin' in xin. discriminate.
 reflexivity.
  change (simplify f2 :: simplify f1 :: f1 :: r :: nil) with ((simplify f2::nil)++(simplify f1 :: f1 :: r :: nil)).
  apply proof_weakening.
  apply p2.
 reflexivity.
 intros x xin. apply prf_uses_ctx with (n:=S x) in p2. apply VarSet.inter_1 in xin.
 simpl in p2. destruct (VarSet.union_1 xin) as [Hx|Hx]; apply VarSet.singleton_1 in Hx; omega.
 apply VarSet.inter_2 in xin. apply shift_down_In. assumption.
 reflexivity. reflexivity.
 intros x xin. apply prf_uses_ctx with (n:=x) in p1. simpl in p1.
 apply VarSet.inter_2 in xin. apply shift_down_In in xin.
 destruct (VarSet.union_1 xin) as [Hx'|Hx]. destruct (VarSet.union_1 Hx') as [Hx|Hx]; apply VarSet.singleton_1 in Hx; unfold VarSet.E.eq in Hx; omega.
 apply prf_uses_ctx with (n:=S (S x)) in p2. simpl in p2. omega.
 apply shift_down_In in Hx. assumption.
 apply VarSet.inter_1 in xin. assumption.
 reflexivity. reflexivity.

Qed.

End ILLSimplifier.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "." "ILL")
   End:
   *)

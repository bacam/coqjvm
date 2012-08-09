Require Import ILLInterfaces.
Require Import BasicMachineTypes.
Require Import ClassResourceAlgebra.
Require Import MLStrings.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require Arith.

Parameter s_top : MLString.
Extract Constant s_top => """TT""".
Parameter s_lb : MLString.
Extract Constant s_lb => """(""".
Parameter s_rb : MLString.
Extract Constant s_rb => """)""".
Parameter s_tens : MLString.
Extract Constant s_tens => """ * """.
Parameter s_and : MLString.
Extract Constant s_and => """ & """.
Parameter s_lolli : MLString.
Extract Constant s_lolli => """ -o """.
Parameter s_bang : MLString.
Extract Constant s_bang => """!""".

(* Workaround for coq bug #2155 - extraction fails for functorial module
   types and "with Definition". *)
Module Type FIDDLE_BASE_SEMANTICS.
  Declare Module B0 : BASICS.
  Include Type ILL_BASE_SEMANTICS B0.
End FIDDLE_BASE_SEMANTICS.

Module ResBaseSemantics (B:BASICS)
                        (F:FILTER B)
  : FIDDLE_BASE_SEMANTICS with Module B0:=B with Definition SYN.atom := B.Classname.t.

Module B0 := B.

Module RA := ClassResourceAlgebra.ClassResourceAlgebra B F.
Module SYN.
  Definition atom := B.Classname.t.
  Definition atom_eq_dec := B.Classname.eq_dec.

  Inductive formula : Set :=
  | f_i      : formula
  | f_atom   : atom -> formula
  | f_tensor : formula -> formula -> formula
  | f_and    : formula -> formula -> formula
  | f_lolli  : formula -> formula -> formula
  | f_bang   : formula -> formula.

  Definition formula_eq_dec : forall (f1 f2 : formula), {f1=f2}+{f1<>f2}.
    decide equality. apply atom_eq_dec.
  Save.

  Inductive axiom_name' : Set := .
  Definition axiom_name := axiom_name'.
  Definition axiom_domain   (a:axiom_name) : formula := match a with end.
  Definition axiom_codomain (a:axiom_name) : formula := match a with end.

  Definition R_new (cls:B.Classname.t) : option atom := if F.f cls then Some cls else None.

  Fixpoint string_of_formula' (f:formula) (prec:nat) {struct f} : MLString :=
    let (s,prec') :=
    match f with
      | f_i => (s_top,7)
      | f_atom a => (B.Classname.to_string a, 7)
      | f_tensor f1 f2 => ((string_of_formula' f1 2) mlapp
                          s_tens mlapp (string_of_formula' f2 3), 2)
      | f_and f1 f2    => ((string_of_formula' f1 0) mlapp
                          s_and mlapp (string_of_formula' f2 1), 0)
      | f_lolli f1 f2  => ((string_of_formula' f1 5) mlapp
                          s_lolli mlapp (string_of_formula' f2 4), 4)
      | f_bang f       => (s_bang mlapp (string_of_formula' f 6), 6)
    end in
    if Compare_dec.le_gt_dec prec prec' then s else s_lb mlapp s mlapp s_rb.

  Definition string_of_formula f := string_of_formula' f 0.


  Module FormulaOrdered <: UsualOrderedType.
    Definition t := formula.
    Definition eq:=@eq t.
    Definition eq_refl := @refl_equal t.
    Definition eq_sym := @sym_eq t.
    Definition eq_trans := @trans_eq t.
    
    Fixpoint lt p q {struct p} : Prop :=
      match p with
      | f_i =>
          match q with | f_i => False | _ => True end
      | f_atom a => 
          match q with
          | f_i => False
          | f_atom b => B.Classname.lt a b
          | _ => True
          end
      | f_tensor a b =>
          match q with
          | f_i | f_atom _ => False
          | f_tensor c d => lt a c \/ (eq a c /\ lt b d)
          | _ => True
          end
      | f_and a b =>
          match q with
          | f_i | f_atom _ | f_tensor _ _ => False
          | f_and c d => lt a c \/ (eq a c /\ lt b d)
          | _ => True
          end
      | f_lolli a b =>
          match q with
          | f_i | f_atom _ | f_tensor _ _ | f_and _ _ => False
          | f_lolli c d => lt a c \/ (eq a c /\ lt b d)
          | _ => True
          end
      | f_bang a =>
          match q with
          | f_bang b => lt a b
          | _ => False
          end
      end.
    
    Hint Resolve B.Classname.lt_trans.
    
    Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
    Proof.
    induction x; destruct z; destruct y; simpl; intuition eauto;
    unfold eq in * |- *; subst; auto.
    Save.
    
    Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
    Proof.
    induction x; destruct y; simpl; intros; unfold eq;
    first [discriminate | contradiction
    | injection; intro atomeq; apply (B.Classname.lt_not_eq H atomeq)
    | injection; intros; inversion H; [apply IHx1 with y1| inversion H3; apply IHx2 with y2]; auto
    | injection; intro; apply IHx with y; auto].
    Save.
    
    Hint Unfold lt eq B.Classname.eq.
    Hint Immediate eq_sym.
    Hint Resolve eq_refl eq_trans lt_trans lt_not_eq.
    Hint Constructors Compare.
    Hint Constructors formula.
    
    Definition compare : forall x y, Compare lt eq x y.
    induction x; destruct y; intuition eauto;
    first
    [ destruct (B.Classname.compare a a0); eauto; apply EQ; rewrite e; auto
    | destruct (IHx1 y1); eauto; destruct (IHx2 y2); eauto;
      [ apply EQ; rewrite e; rewrite e0; auto
      | apply GT; simpl; right; split;auto]
    | destruct (IHx y); eauto; apply EQ; rewrite e; auto].
    Save.
    
    Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    Proof.
      intros; elim (compare x y); intro H; [ right | left | right ]; auto using lt_not_eq.
      assert (~ eq y x); auto using lt_not_eq, eq_sym.
    Defined.
    
  End FormulaOrdered.
End SYN.

Definition res_of_atom (a:B.Classname.t) := match RA.r_new a with None => RA.e | Some r => r end.

Lemma r_new_match : forall cls_nm r, RA.r_new cls_nm = Some r -> exists a, SYN.R_new cls_nm = Some a /\ res_of_atom a = r.
Proof.
  intros. exists cls_nm. unfold res_of_atom, RA.r_new, SYN.R_new in *. rewrite H. destruct (F.f cls_nm); intuition. discriminate.
Qed.

Lemma r_new_empty : forall cls_nm  , RA.r_new cls_nm = None -> SYN.R_new cls_nm = None.
Proof.
  intros. unfold RA.r_new, SYN.R_new in *. destruct (F.f cls_nm). discriminate. reflexivity.
Qed.

Fixpoint sat (r:RA.res) (A:SYN.formula) {struct A} : Prop
 :=
 match A with
 | SYN.f_i          => True
 | SYN.f_atom a     => RA.leq (res_of_atom a) r
 | SYN.f_tensor A B => exists r1, exists r2, RA.leq (RA.combine r1 r2) r /\ sat r1 A /\ sat r2 B
 | SYN.f_and A B    => sat r A /\ sat r B
 | SYN.f_lolli A B  => forall r', sat r' A -> sat (RA.combine r r') B
 | SYN.f_bang A     => exists r', RA.leq (RA.bang r') r /\ sat r' A
 end.

Lemma axioms_sound : forall ax r,
  sat r (SYN.axiom_domain ax) -> sat r (SYN.axiom_codomain ax).
Proof.
  intros.
  inversion ax.
Qed.

End ResBaseSemantics.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "." "ILL")
   End:
   *)

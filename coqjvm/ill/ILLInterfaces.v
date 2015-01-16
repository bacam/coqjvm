Require Import BasicMachineTypes.
Require Import ResourceAlgebra.
Require Import FSetInterface.
Require Import FSetProperties.
Require Import OrderedTypeEx.
Require Setoid.
Require MLStrings.

Module Type ILL_BASE_SYNTAX (B : BASICS).

Parameter atom : Set.
Parameter atom_eq_dec : forall (a1 a2:atom), {a1=a2}+{a1<>a2}.

Inductive formula : Set :=
| f_i      : formula
| f_atom   : atom -> formula
| f_tensor : formula -> formula -> formula
| f_and    : formula -> formula -> formula
| f_lolli  : formula -> formula -> formula
| f_bang   : formula -> formula.

Parameter formula_eq_dec : forall (f1 f2 : formula), {f1=f2}+{f1<>f2}.

Parameter axiom_name     : Set.
Parameter axiom_domain   : axiom_name -> formula.
Parameter axiom_codomain : axiom_name -> formula.

Parameter R_new : B.Classname.t -> option atom.

Parameter string_of_formula : formula -> MLStrings.MLString.

Declare Module FormulaOrdered : UsualOrderedType with Definition t:=formula.

End ILL_BASE_SYNTAX.

Module Type ILL_SYNTAX
  (B : BASICS)
  (BASESYN : ILL_BASE_SYNTAX B).

Import BASESYN.

Inductive prf_term : Set :=
| t_lvar         : nat -> prf_term
| t_ivar         : nat -> prf_term
| t_i_intro      : prf_term
| t_tensor_intro : prf_term -> prf_term -> prf_term
| t_tensor_elim  : prf_term -> prf_term -> prf_term
| t_and_intro    : prf_term -> prf_term -> prf_term
| t_and_elim1    : prf_term -> prf_term
| t_and_elim2    : prf_term -> prf_term
| t_lolli_intro  : formula -> prf_term -> prf_term
| t_lolli_elim   : prf_term -> prf_term -> prf_term
| t_bang_intro   : prf_term -> prf_term
| t_bang_elim    : prf_term -> prf_term -> prf_term
| t_axiom        : axiom_name -> prf_term -> prf_term
| t_let          : prf_term -> prf_term -> prf_term.

Declare Module VarSet : FSetInterface.S with Definition E.t := nat with Definition E.eq := (@eq nat).
Module VarSetProps := Properties VarSet.

Definition shift_step n s := match n with O => s | S n => VarSet.add n s end.
Definition shift_down s := VarSet.fold shift_step s VarSet.empty.
Declare Instance shift_down_mor_Proper : Proper (VarSet.Equal ==> VarSet.Equal) shift_down.
Parameter In_shift_down : forall n U,  VarSet.In (S n) U -> VarSet.In n (shift_down U).
Parameter shift_down_In : forall n U,  VarSet.In n (shift_down U) -> VarSet.In (S n) U.

Definition context := list formula.

Inductive prf : context -> context -> prf_term -> formula -> VarSet.t -> Prop :=
| prf_ivar : forall Gi G n A U,
   nth_error Gi n = Some A ->
   VarSet.Equal U VarSet.empty ->
   prf Gi G (t_ivar n) A U
| prf_lvar : forall Gi G n A U,
   nth_error G n = Some A ->
   VarSet.Equal U (VarSet.singleton n) ->
   prf Gi G (t_lvar n) A U
| prf_i_intro : forall Gi G U,
   VarSet.Equal U VarSet.empty ->
   prf Gi G t_i_intro f_i U
| prf_tensor_intro : forall Gi G t1 t2 A B U1 U2 U,
   prf Gi G t1 A U1 ->
   prf Gi G t2 B U2 ->
   VarSet.Empty (VarSet.inter U1 U2) ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_tensor_intro t1 t2) (f_tensor A B) U
| prf_tensor_elim : forall Gi G t1 t2 A B C U1 U2 U,
   prf Gi G t1 (f_tensor A B) U1 ->
   prf Gi (A::B::G) t2 C U2 ->
   VarSet.Empty (VarSet.inter U1 (shift_down (shift_down U2))) ->
   VarSet.Equal U (VarSet.union U1 (shift_down (shift_down U2))) ->
   prf Gi G (t_tensor_elim t1 t2) C U
| prf_and_intro : forall Gi G t1 t2 A B U1 U2 U,
   prf Gi G t1 A U1->
   prf Gi G t2 B U2 ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_and_intro t1 t2) (f_and A B) U
| prf_and_elim1 : forall Gi G t A B U,
   prf Gi G t (f_and A B) U ->
   prf Gi G (t_and_elim1 t) A U
| prf_and_elim2 : forall Gi G t A B U,
   prf Gi G t (f_and A B) U ->
   prf Gi G (t_and_elim2 t) B U
| prf_lolli_intro : forall Gi G t A B Ut U,
   prf Gi (A::G) t B Ut ->
   VarSet.Equal U (shift_down Ut) ->
   prf Gi G (t_lolli_intro A t) (f_lolli A B) U
| prf_lolli_elim : forall Gi G t1 t2 A B U1 U2 U,
   prf Gi G t1 (f_lolli A B) U1 ->
   prf Gi G t2 A U2 ->
   VarSet.Empty (VarSet.inter U1 U2) ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_lolli_elim t1 t2) B U
| prf_bang_intro : forall Gi G t A U,
   prf Gi G t A U ->
   VarSet.Empty U ->
   prf Gi G (t_bang_intro t) (f_bang A) U
| prf_bang_elim : forall Gi G t1 t2 A B U1 U2 U,
   prf Gi G t1 (f_bang A) U1 ->
   prf (A::Gi) G t2 B U2 ->
   VarSet.Empty (VarSet.inter U1 U2) ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_bang_elim t1 t2) B U
| prf_axiom : forall Gi G t ax U,
   prf Gi G t (axiom_domain ax) U ->
   prf Gi G (t_axiom ax t) (axiom_codomain ax) U
| prf_let : forall Gi G t1 t2 A B U1 Ut2 U2 U,
   prf Gi G t1 A U1 ->
   prf Gi (A::G) t2 B Ut2 ->
   VarSet.Equal U2 (shift_down Ut2) ->
   VarSet.Empty (VarSet.inter U1 U2) ->
   VarSet.Equal U (VarSet.union U1 U2) ->
   prf Gi G (t_let t1 t2) B U.

Parameter proof_check : forall Gi G (t:prf_term),
  { B : formula | exists U, prf Gi G t B U }+{True}.

Definition implies : formula -> formula -> Prop :=
  fun A B => exists t, exists U, prf nil (A::nil) t B U.

Axiom implies_refl : forall A, implies A A.
Axiom implies_trans : forall A B C, implies A B -> implies B C -> implies A C.
Axiom implies_subformulae : forall f1 f2 f1' f2' fo,
  implies f1 f1' -> implies f2 f2' -> fo = f_tensor \/ fo = f_and ->
  implies (fo f1 f2) (fo f1' f2').
(*
Axiom implies_lolli : forall f1 f2 f1' f2',
  implies f1 f1' -> implies f2 f2' ->
  implies (f_lolli f1' f2) (f_lolli f1 f2').
*)


Parameter proof_check_single : forall A B (t:prf_term),
  { implies A B }+{True}.


Axiom prf_uses_ctx : forall Gi G t A U,
 prf Gi G t A U -> forall n, VarSet.In n U -> n < length G.
(* There's a stronger version of this in the implementation, but it requires
   more work to use. *)
Axiom proof_weakening : forall Gi G G' t A U,
 prf Gi G t A U -> prf Gi (G++G') t A U.

Definition r_may := fun c f =>
  match R_new c with
    | None => f_i
    | Some r => f r
  end.

Definition resexpr_to_formula : res_expr B.Classname.t -> formula := 
let r_to_f_step (f:formula) (r:res_expr B.Classname.t) :=
  List.fold_left (fun f expr =>
    f_tensor f (match expr with (true,c) => r_may c (fun r => f_bang (f_atom r)) | (false,c) => r_may c (fun r => f_atom r) end))
    r f
in r_to_f_step f_i.

End ILL_SYNTAX.

Module Type ILL_BASE_SEMANTICS (B : BASICS).

Declare Module RA : RESOURCE_ALGEBRA B.
Declare Module SYN : ILL_BASE_SYNTAX B.

Parameter res_of_atom : SYN.atom -> RA.res.

Axiom r_new_match : forall cls_nm r, RA.r_new cls_nm = Some r -> exists a, SYN.R_new cls_nm = Some a /\ res_of_atom a = r.
Axiom r_new_empty : forall cls_nm  , RA.r_new cls_nm = None -> SYN.R_new cls_nm = None.

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

Axiom axioms_sound : forall ax r,
  sat r (SYN.axiom_domain ax) -> sat r (SYN.axiom_codomain ax).

End ILL_BASE_SEMANTICS.

Module Type ILL_SEMANTICS
  (B   : BASICS)
  (BASESEM : ILL_BASE_SEMANTICS B)
  (SYN : ILL_SYNTAX B BASESEM.SYN).

Import SYN.
Import BASESEM.

Fixpoint context_to_formula (G:context) (n:nat) (U:VarSet.t)
                            {struct G}
                          : SYN.formula :=
  match G with
  | nil => SYN.f_i
  | cons f rest => if VarSet.mem n U then SYN.f_tensor f (context_to_formula rest (S n) U)
                                         else context_to_formula rest (S n) U
  end.

Fixpoint icontext_to_formula (G:context) : SYN.formula :=
  match G with
  | nil => SYN.f_i
  | cons f rest => SYN.f_tensor f (icontext_to_formula rest)
  end.

Axiom soundness : forall r Gi G t A U,
  prf Gi G t A U ->
  sat r (SYN.f_tensor (SYN.f_bang (icontext_to_formula Gi)) (context_to_formula G 0 U)) ->
  sat r A.

Axiom single_soundness : forall r A B t U,
  sat r A ->
  prf nil (A::nil) t B U ->
  sat r B.

Axiom implies_soundness : forall r A B,
  sat r A ->
  implies A B ->
  sat r B.

Axiom sat_leq : forall r1 r2 A,
  sat r1 A -> RA.leq r1 r2 -> sat r2 A.


Axiom res_formula : forall re:res_expr B.Classname.t,
  sat (RA.res_parse re) (resexpr_to_formula re).

End ILL_SEMANTICS.

(*
   Local Variables:
   coq-prog-args: ("-emacs-U" "-I" ".." "-R" "." "ILL")
   End:
   *)





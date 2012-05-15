Require Import OptionExt.

(* option monad *)
Definition ret := fun (A:Type) (a:A) => Some a.
Definition bind : forall (A B:Type), option A -> (A -> option B) -> option B :=
  fun A B a f =>
  match a with
  | None => None
  | Some a => f a
  end.
Definition fail := fun (A:Type) => None (A:=A).

Implicit Arguments bind [A B].
Implicit Arguments ret [A].
Implicit Arguments fail [A].

Definition lift_bool : bool -> option unit := fun b => if b then ret tt else fail.

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 20, right associativity).
Notation "x <- c1 ;: c2" := (bind c1 (fun x => c2)) (at level 20, right associativity).

(* Tactics for option monad handling *)
Ltac destruct_opt t t' result resulteq :=
  destruct (option_dec t) as [[result resulteq] | resulteq];
  rewrite resulteq in t';
  [simpl in t' | discriminate].

Ltac ret_inject t :=
  unfold ret in t; injection t; clear t; intro t.

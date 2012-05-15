type formula_absyn =
  | F_top
  | F_atom of string
  | F_tensor of formula_absyn * formula_absyn
  | F_and of formula_absyn * formula_absyn
  | F_lolli of formula_absyn * formula_absyn
  | F_bang of formula_absyn

type term_absyn =
  | T_var of string
  | T_star
  | T_tensor_intro of term_absyn * term_absyn
  | T_tensor_elim of string * string * term_absyn * term_absyn
  | T_lolli_intro of string * formula_absyn * term_absyn
  | T_lolli_elim of term_absyn * term_absyn
  | T_bang_intro of term_absyn
  | T_bang_elim of string * term_absyn * term_absyn
  | T_and_intro of term_absyn * term_absyn
  | T_and_elim1 of term_absyn
  | T_and_elim2 of term_absyn
  | T_axiom of string * term_absyn
  | T_let of string * term_absyn * term_absyn

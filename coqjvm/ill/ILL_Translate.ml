open Ill_absyn
open CoqModules
open TranslateTools

let get_pos x l =
  let rec loop n l = match l with
    | [] -> None
    | (y::l) -> if x = y then Some n else loop (Common.Types.S n) l
  in loop Common.Types.O l

let rec formula_to_coq f = match f with
  | F_top -> ResILLBase.SYN.Coq_f_i
  | F_atom s -> (match ResILLBase.SYN.coq_R_new (class_of_string s) with None -> ResILLBase.SYN.Coq_f_i | Some a -> ResILLBase.SYN.Coq_f_atom a)
  | F_tensor (f1,f2) -> ResILLBase.SYN.Coq_f_tensor (formula_to_coq f1, formula_to_coq f2)
  | F_and (f1,f2) -> ResILLBase.SYN.Coq_f_and (formula_to_coq f1, formula_to_coq f2)
  | F_lolli (f1,f2) -> ResILLBase.SYN.Coq_f_lolli (formula_to_coq f1, formula_to_coq f2)
  | F_bang f -> ResILLBase.SYN.Coq_f_bang (formula_to_coq f)

let rec term_to_coq gi g t = match t with
  | T_var v ->
      (match get_pos v gi with
	 | Some n -> ILL.Coq_t_ivar n
	 | None ->
	     (match get_pos v g with
		| Some n -> ILL.Coq_t_lvar n
		| None -> failwith ("Variable " ^ v ^ " not found")))
  | T_star -> ILL.Coq_t_i_intro
  | T_tensor_intro (t1, t2) ->
      ILL.Coq_t_tensor_intro (term_to_coq gi g t1, term_to_coq gi g t2)
  | T_tensor_elim (v1, v2, t1, t2) ->
      ILL.Coq_t_tensor_elim (term_to_coq gi g t1, term_to_coq gi (v1::v2::g) t2)
  | T_and_intro (t1, t2) ->
      ILL.Coq_t_and_intro (term_to_coq gi g t1, term_to_coq gi g t2)
  | T_and_elim1 t ->
      ILL.Coq_t_and_elim1 (term_to_coq gi g t)
  | T_and_elim2 t ->
      ILL.Coq_t_and_elim2 (term_to_coq gi g t)
  | T_lolli_intro (v,f,t) ->
      ILL.Coq_t_lolli_intro (formula_to_coq f, term_to_coq gi (v::g) t)
  | T_lolli_elim (t1, t2) ->
      ILL.Coq_t_lolli_elim (term_to_coq gi g t1, term_to_coq gi g t2)
  | T_bang_intro t ->
      ILL.Coq_t_bang_intro (term_to_coq gi g t)
  | T_bang_elim (v,t1,t2) ->
      ILL.Coq_t_bang_elim (term_to_coq gi g t1, term_to_coq (v::gi) g t2)
  | T_axiom (ax,t) ->
      failwith "There are no axioms"
(*      ILL.Coq_t_axiom (ResILLBase.SYN.parse_axiom ax, term_to_coq gi g t)*)
  | T_let (v,t1,t2) ->
      ILL.Coq_t_let (term_to_coq gi g t1, term_to_coq gi (v::g) t2)

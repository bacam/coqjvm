open Ill_absyn
open ILL_Translate
open CoqModules

let print_formula f = ResILLBase.SYN.string_of_formula (formula_to_coq f)

let rec print_term t = match t with
  | T_var s -> s
  | T_star -> "tt"
  | T_tensor_intro (t1, t2) -> "(" ^ print_term t1 ^ " * " ^ print_term t2 ^ ")"
  | T_tensor_elim (v1, v2, t1, t2) -> "let " ^ v1 ^ "*" ^ v2 ^ " be " ^ print_term t1 ^ " in " ^ print_term t2 ^ " end"
  | T_lolli_intro (v, f, t) ->  "(@" ^ v ^ " : " ^ print_formula f ^ ". " ^ print_term t ^ ")"
  | T_lolli_elim (t1, t2) -> "(" ^ print_term t1 ^ " " ^ print_term t2 ^ ")"
  | T_bang_intro t -> "!" ^ print_term t
  | T_bang_elim (v,t1,t2) -> "let !" ^ v ^ " be " ^ print_term t1 ^ " in " ^ print_term t2 ^ " end"
  | T_and_intro (t1, t2) -> "(" ^ print_term t1 ^ " & " ^ print_term t2 ^ ")"
  | T_and_elim1 t -> "#1(" ^ print_term t ^ ")"
  | T_and_elim2 t -> "#2(" ^ print_term t ^ ")"
  | T_axiom (ax,t) -> "$" ^ ax ^ "(" ^ print_term t ^ ")" 
  | T_let (v,t1,t2) -> "let " ^ v ^ " be " ^ print_term t1 ^ " in " ^ print_term t2 ^ " end"

let _ =
  let lexbuf = Lexing.from_channel stdin in
  let to_check = Ill_parser.input Ill_lexer.token lexbuf in
  let run_check (a,b,t,e) =
    let a2 = formula_to_coq a in
    let b2 = formula_to_coq b in
    let t2 = term_to_coq [] ["x"] t in
    let estr = if e then "ok" else "fail" in
      (if ILL.proof_check_single a2 b2 t2 = e then
	   print_string ("PASS (expected "^ estr ^ ")\n")
       else
	   print_string ("FAIL (expected "^ estr ^ ")\n"));
      print_string ("  hypothesis : " ^ print_formula a ^ "\n");
      print_string ("  conclusion : " ^ print_formula b ^ "\n");
      print_string ("  proof      : " ^ print_term t ^ "\n");
      print_newline ()
  in
    List.iter run_check to_check



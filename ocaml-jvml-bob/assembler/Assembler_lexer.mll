{
  open Assembler_parser
  open Lexing

(* stolen from links *)
let bump_lines ?(count=1) lexbuf =
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_lnum = lexbuf.lex_curr_p.pos_lnum + count; pos_bol = lexbuf.lex_curr_p.pos_cnum + 1 }

let bump_lines_from_string lexbuf str =
  let newlines = ref 0 in
    String.iter (fun c -> if c = '\n' then incr newlines) str;
    bump_lines ~count:!newlines lexbuf
}

let ident = [^' ' '\t' '\n']

rule token = parse
    [' ' '\t']+       { token lexbuf }
  | ';' [^'\n']* '\n' { bump_lines lexbuf; token lexbuf }
  | '\n'              { bump_lines lexbuf; NEWLINE }
  | '.' (ident+ as s)  { DIRECTIVE s }
  | '"'               { STRINGLIT (str [] lexbuf) }
  | ([^' ' '\t' '\n' '"'] ident*) as s { WORD s }
  | eof               { EOF }
(*  | (_ as c)          { Printf.printf "Odd: %c\n" c; flush stdout; WORD (String.make 1 c) } *)

and str l = parse
    '"'               { String.concat "" (List.rev l) }
  | [^'"' '\\']+ as s { bump_lines_from_string lexbuf s; str (s::l) lexbuf }
  | '\\' (_ as c) { str ((String.make 1 c)::l) lexbuf }

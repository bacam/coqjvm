{
  open Ill_parser
}

rule token = parse
    [' ' '\t' '\n'] { token lexbuf }
  | '%' [^'\n']* '\n' { token lexbuf }
  | '*'             { TENSOR }
  | "&"             { AND }
  | "-o"            { LOLLI }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | "let"           { LET }
  | "be"            { BE }
  | "in"            { IN }
  | "@"             { LAMBDA }
  | ':'             { COLON }
  | '.'             { DOT }
  | '!'             { BANG }
  | "tt"            { STAR }
  | "TT"            { TOP }
  | "#1"            { P1 }
  | "#2"            { P2 }
  | '$'['A'-'Z''a'-'z''_']['A'-'Z''a'-'z''_''0'-'9']* as id
                    { AXIOM (String.sub id 1 (String.length id - 1)) }
  | "end"           { END }
  | "OK"            { OK }
  | "FAIL"          { FAIL }
  | ['A'-'Z''a'-'z''_']['A'-'Z''a'-'z''_''0'-'9''.']* as id
                    { ID id }
  | eof             { EOF }
  | _ as x          { failwith ("Unknown token: " ^ String.make 1 x) }

{
  open Parser
  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")

  let unterminated_string () =
    raise (Error "unterminated string")

}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "."     { DOT }
  | "("     { LPAREN }
  | ")"     { RPAREN }
  | ":"     { COLON }
  | "+"     { PLUS }
  | "@"     { AT }
  | "-"     { MINUS }  
  | "*"     { STAR }
  | "["     { LBRACKET }
  | "]"     { RBRACKET }
  | "challenge" { CHALLENGE }
  | "forall" { FORALL }
  | "input" { INPUT }
  | "in" { IN }
  | "setting" { SETTING }
  | "symmetric" { SYMMETRIC }
  | "asymmetric" { ASYMMETRIC }
  | "computational" { COMPUTATIONAL }
  | "decisional" { DECISIONAL }
  | "problem_type" {PROBLEM_TYPE}
  | "arity" { ARITY }
  | ['0'-'9']['0'-'9']* as s { NAT(int_of_string(s)) }
  | ['l']                { RLIMIT(-1) } (* l0 and l refer to the same variable *)
  | ['l']['0'-'9']* as s { RLIMIT(int_of_string(String.sub s 1 (String.length s - 1))) }

  | ['a'-'k' 'm'-'z']
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*
    as s { LID s }
  | ['A'-'Z']
    ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']*
    as s { UID s }
  | ","     { COMMA }
  | "^"     { CARET }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

and string buf = parse
  | "\""          { buf }
  | "\\n"         { Buffer.add_char buf '\n'; string buf lexbuf }
  | "\\r"         { Buffer.add_char buf '\r'; string buf lexbuf }
  | "\\" (_ as c) { Buffer.add_char buf c   ; string buf lexbuf }
  | newline       { Buffer.add_string buf (Lexing.lexeme lexbuf); string buf lexbuf }
  | _ as c        { Buffer.add_char buf c   ; string buf lexbuf }

  | eof           { unterminated_string () }
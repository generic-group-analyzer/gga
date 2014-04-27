(*s Lexer for parametric assumptions. *)
{
  (*i*)
  open ParamParser

  module S = String
  (*i*)

  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")

  let unterminated_string () =
    raise (Error "unterminated string")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'
let idchars = ['a'-'z' 'A'-'Z' '\'' '_' '0'-'9']

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
  | ","     { COMMA }
  | "^"     { CARET }

  | "challenge"     { CHALLENGE }
  | "forall"        { FORALL }
  | "input"         { INPUT }
  | "in"            { IN }
  | "setting"       { SETTING }
  | "symmetric"     { SYMMETRIC }
  | "asymmetric"    { ASYMMETRIC }
  | "computational" { COMPUTATIONAL }
  | "decisional"    { DECISIONAL }
  | "problem_type"  { PROBLEM_TYPE }
  | "levels"        { LEVELS }

  | ['0'-'9']['0'-'9']* as s { NAT(int_of_string(s)) }
  | ['l']                    { RLIMIT(-1) }
  | ['l']['0'-'9']* as s     { RLIMIT(int_of_string(S.sub s 1 (S.length s - 1))) }
  | ['a'-'j' 'm'-'z']idchars* as s { VARL s }
  | ['k']                          { VARLEVEL }
  | ['A'-'Z']idchars*         as s { VARU s }

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
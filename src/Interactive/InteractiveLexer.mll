(*s Lexer for interactive assumptions *)
{
  (*i*)
  open InteractiveParser

  module S = String
  (*i*)

  exception Error of string

  let unterminated_comment () =
    raise (Error "unterminated comment")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'
let idchars = ['a'-'z' 'A'-'Z' '0'-'9']

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "."     { DOT }
  | "("     { LPAR }
  | ")"     { RPAR }
  | "="     { EQ }
  | "->"    { TO }  
  | "/\\"   { LAND }
  | "<>"    { INEQ }
  | "+"     { PLUS }
  | "-"     { MINUS }
  | "*"     { STAR }
  | "^"     { EXP }
  | "["     { LBRACK }
  | "]"     { RBRACK }
  | ","     { COMMA }
  | ";"     { SEMICOLON }
  | ":"     { COLON }
  | "sample" { SAMP }
  | "maps"   { EMAPS }
  | "isos"   { ISOS }
  | "map"    { EMAPS }
  | "iso"    { ISOS }
  | "forall" { FORALL }
  | "_" { UNDERSCORE }

  | "return" { RETURN }
  | "input"  { INP }
  | "oracle" { ORACLE }
  | "win"    { WIN }
  | "in"     { IN }

  | ['G']idchars* as s { GROUP (S.sub s 1 (S.length s - 1)) }
  | "Fp" { FIELD }

  | ['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | '-'['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | ['A'-'F' 'H'-'Z' 'a'-'z']idchars* as s { VAR s }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

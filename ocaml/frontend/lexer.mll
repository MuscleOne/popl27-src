{
open Parser
exception Error of string

let keyword = function
  | "int" -> TINT | "bool" -> TBOOL | "unit" -> TUNIT
  | "id" -> TID | "sexp" -> TSEXP
  | "true" -> TRUE | "false" -> FALSE
  | "fun" -> FUN | "fix" -> FIX | "is" -> IS
  | "let" -> LET | "in" -> IN
  | "if" -> IF | "then" -> THEN | "else" -> ELSE
  | "async" -> ASYNC | "match" -> MATCH
  | "Int" -> CINT | "Bool" -> CBOOL | "Id" -> CID
  | "Nil" -> NIL | "Pair" -> PAIR | "_" -> UNDERSCORE
  | name -> VAR name
}

let digit = ['0'-'9']
let name = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']*

rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | "(*" { comment 1 lexbuf; token lexbuf }
  | digit+ { INT (Z.of_string (Lexing.lexeme lexbuf)) }
  | name { keyword (Lexing.lexeme lexbuf) }
  | '"' { ID (identifier (Buffer.create 16) lexbuf) }
  | '(' { LPAREN } | ')' { RPAREN }
  | '{' { LBRACE } | '}' { RBRACE }
  | ':' { COLON } | ',' { COMMA } | '|' { BAR }
  | '+' { PLUS } | '-' { MINUS } | '*' { STAR }
  | '=' { EQ } | '<' { LT }
  | "->" { ARROW } | "=>" | "⇒" { BRANCH }
  | ";;" { SEMISEMI }
  | eof { EOF }
  | _ { raise (Error (Printf.sprintf "Unexpected character %S" (Lexing.lexeme lexbuf))) }

and comment depth = parse
  | "(*" { comment (depth + 1) lexbuf }
  | "*)" { if depth > 1 then comment (depth - 1) lexbuf }
  | '\n' { Lexing.new_line lexbuf; comment depth lexbuf }
  | eof { raise (Error "Unterminated comment") }
  | _ { comment depth lexbuf }

and identifier buffer = parse
  | '"' { Buffer.contents buffer }
  | '\\' ('"' | '\\' as c) { Buffer.add_char buffer c; identifier buffer lexbuf }
  | "\\n" { Buffer.add_char buffer '\n'; identifier buffer lexbuf }
  | "\\r" { Buffer.add_char buffer '\r'; identifier buffer lexbuf }
  | "\\t" { Buffer.add_char buffer '\t'; identifier buffer lexbuf }
  | "\\b" { Buffer.add_char buffer '\b'; identifier buffer lexbuf }
  | '\\' (digit digit digit as digits) {
      let code = int_of_string digits in
      if code > 255 then raise (Error "Identifier escape is outside 000--255");
      Buffer.add_char buffer (Char.chr code); identifier buffer lexbuf
    }
  | '\\' _ { raise (Error "Unknown identifier escape") }
  | '\n' { Lexing.new_line lexbuf; raise (Error "Use \\n inside an identifier literal") }
  | eof { raise (Error "Unterminated identifier literal") }
  | _ as c { Buffer.add_char buffer c; identifier buffer lexbuf }

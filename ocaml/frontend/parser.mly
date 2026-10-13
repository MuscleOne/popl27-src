%{
open Parsed_syntax

(* Parentheses group terms but do not make non-atomic terms into atoms. *)
let as_atom = function
  | Atom a -> a
  | _ -> raise (Invalid_syntax "Expected an atom; bind this term with let first")
%}

%token <string> VAR ID
%token <Z.t> INT
%token TINT TBOOL TUNIT TID TSEXP TRUE FALSE
%token FUN FIX IS LET IN IF THEN ELSE ASYNC MATCH
%token CINT CBOOL CID NIL PAIR UNDERSCORE
%token LPAREN RPAREN LBRACE RBRACE COLON COMMA BAR
%token PLUS MINUS STAR EQ LT ARROW BRANCH SEMISEMI EOF

%start <Parsed_syntax.term Zoo.located list> file
%start <Parsed_syntax.term Zoo.located> toplevel

%%

file:
  | EOF { [] }
  | c = command EOF { [c] }
  | c = command SEMISEMI rest = file { c :: rest }

toplevel:
  | c = command EOF { c }
  | c = command SEMISEMI EOF { c }

command:
  | t = term { Zoo.locate ~loc:(Zoo.make_location $startpos $endpos) t }

term:
  | t = simple_term { t }
  | fn = simple_term LPAREN args = separated_nonempty_list(COMMA, term) RPAREN
      { Apply (as_atom fn, List.map as_atom args) }
  | left = simple_term op = operator right = simple_term
      { Operation (as_atom left, op, as_atom right) }
  | LET x = name EQ rhs = term IN body = term { Let (x, rhs, body) }
  | IF guard = term THEN yes = term ELSE no = term
      { If (as_atom guard, yes, no) }
  | ASYNC body = term { Async body }
  | MATCH a = term LBRACE branches = separated_nonempty_list(BAR, branch) RBRACE
      { Match (as_atom a, branches) }
  | FUN LPAREN ps = separated_nonempty_list(COMMA, parameter) RPAREN
      COLON result = ty IS body = term { Atom (Value (Fun (ps, result, body))) }
  | FIX f = name LPAREN ps = separated_nonempty_list(COMMA, parameter) RPAREN
      COLON result = ty IS body = term { Atom (Value (Fix (f, ps, result, body))) }

simple_term:
  | x = name { Atom (Variable x) }
  | n = INT { Atom (Value (Integer n)) }
  | MINUS n = INT { Atom (Value (Integer (Z.neg n))) }
  | TRUE { Atom (Value (Boolean true)) }
  | FALSE { Atom (Value (Boolean false)) }
  | s = ID { Atom (Value (Identifier (Id.of_string s))) }
  | LPAREN RPAREN { Atom (Value Unit) }
  | LPAREN t = term RPAREN { t }
  | CINT LPAREN t = term RPAREN { Atom (Value (Sexp_int (as_atom t))) }
  | CBOOL LPAREN t = term RPAREN { Atom (Value (Sexp_bool (as_atom t))) }
  | CID LPAREN t = term RPAREN { Atom (Value (Sexp_id (as_atom t))) }
  | NIL { Atom (Value Nil) }
  | PAIR LPAREN a = term COMMA b = term RPAREN
      { Atom (Value (Pair (as_atom a, as_atom b))) }

branch:
  | p = pattern BRANCH body = term { Branch (p, body) }

pattern:
  | CINT LPAREN x = name RPAREN { P_int x }
  | CBOOL LPAREN x = name RPAREN { P_bool x }
  | CID LPAREN x = name RPAREN { P_id x }
  | NIL { P_nil }
  | PAIR LPAREN x = name COMMA y = name RPAREN { P_pair (x, y) }
  | UNDERSCORE { P_wildcard }

parameter:
  | x = name COLON t = ty { (x, t) }

name:
  | x = VAR { x }

ty:
  | TINT { int_ty }
  | TBOOL { bool_ty }
  | TUNIT { unit_ty }
  | TID { id_ty }
  | TSEXP { sexp_ty }
  | LPAREN ts = separated_nonempty_list(COMMA, ty) RPAREN ARROW t = ty
      { arrow ts t }

operator:
  | PLUS { Add }
  | MINUS { Sub }
  | STAR { Mul }
  | EQ { Eq }
  | LT { Lt }

type command =
  (Source_calculus.Syntax.term Zoo.located, Zoo.location * string) result

exception Resolution_error of Zoo.location * string

let parse parser lexbuf =
  try Ok (parser Lexer.token lexbuf) with
  | Lexer.Error message | Source_calculus.Syntax.Invalid_syntax message ->
      Error (Zoo.location_of_lex lexbuf, message)
  | Resolution_error (loc, message) -> Error (loc, message)
  | Parser.Error ->
      let token = Lexing.lexeme lexbuf in
      let message =
        if token = "" then "Unexpected end of input"
        else Printf.sprintf "Unexpected token %S" token
      in
      Error (Zoo.location_of_lex lexbuf, message)

let resolve free command =
  try Zoo.locate ~loc:command.Zoo.loc (Resolve.term ~free command.Zoo.data)
  with Source_calculus.Syntax.Invalid_syntax message ->
    raise (Resolution_error (command.Zoo.loc, message))

let file ?(free = []) lexbuf =
  match
    parse
      (fun token input -> List.map (resolve free) (Parser.file token input))
      lexbuf
  with
  | Ok commands -> List.map (fun command -> Ok command) commands
  | Error error -> [ Error error ]

let toplevel ?(free = []) lexbuf =
  (* Name interactive input so Zoo reports the lexer's one-based line numbers. *)
  if lexbuf.Lexing.lex_curr_p.Lexing.pos_fname = "" then
    lexbuf.Lexing.lex_curr_p <-
      { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "<stdin>" };
  parse (fun token input -> resolve free (Parser.toplevel token input)) lexbuf

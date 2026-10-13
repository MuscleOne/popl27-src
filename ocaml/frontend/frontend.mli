type command =
  (Source_calculus.Syntax.term Zoo.located, Zoo.location * string) result
(** Read the existing source syntax; no ANF conversion or added term forms. *)

val file :
  ?free:(string * Source_calculus.Syntax.Var.t) list ->
  Lexing.lexbuf ->
  command list

val toplevel :
  ?free:(string * Source_calculus.Syntax.Var.t) list -> Lexing.lexbuf -> command
(** Parse errors are returned so that the driver can report them through Zoo
    without its generic parser wrapper discarding the diagnostic message. *)

(** Free names are shared within one command. Supply [free] to reuse identities
    across commands; bound names shadow this association. Both names and
    identities in [free] must be distinct. *)

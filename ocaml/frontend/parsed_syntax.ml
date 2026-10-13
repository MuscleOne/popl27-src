(* Text syntax before name resolution, following Bindlib examples/parsed.ml. *)
include Common_syntax

type pattern =
  | P_int of string
  | P_bool of string
  | P_id of string
  | P_nil
  | P_pair of string * string
  | P_wildcard

type value =
  | Integer of Z.t
  | Boolean of bool
  | Unit
  | Identifier of Id.t
  | Fun of (string * ty) list * ty * term
  | Fix of string * (string * ty) list * ty * term
  | Sexp_int of atom
  | Sexp_bool of atom
  | Sexp_id of atom
  | Nil
  | Pair of atom * atom

and atom = Variable of string | Value of value

and term =
  | Atom of atom
  | Apply of atom * atom list
  | Operation of atom * op * atom
  | If of atom * term * term
  | Let of string * term * term
  | Match of atom * branch list
  | Async of term

and branch = Branch of pattern * term

(* Shared types, primitive operators and identifier literals; no terms or bindings. *)
module Id = struct
  type t = string

  let of_string x = x
  let to_string x = x
  let equal = String.equal
end

exception Invalid_syntax of string

let require condition message =
  if not condition then raise (Invalid_syntax message)

type ty =
  | Ty_int
  | Ty_bool
  | Ty_unit
  | Ty_id
  | Ty_sexp
  | Ty_arrow of ty list * ty

let int_ty = Ty_int
let bool_ty = Ty_bool
let unit_ty = Ty_unit
let id_ty = Ty_id
let sexp_ty = Ty_sexp

let arrow arguments result =
  require (arguments <> []) "A function type needs at least one argument type";
  Ty_arrow (arguments, result)

let equal_ty (left : ty) (right : ty) = left = right

type op = Add | Sub | Mul | Eq | Lt

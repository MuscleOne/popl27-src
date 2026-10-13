(** Definitions shared by the sequential and runtime calculi. *)
module Id : sig
  type t

  val of_string : string -> t
  val to_string : t -> string
  val equal : t -> t -> bool
end

exception Invalid_syntax of string

type ty = private
  | Ty_int
  | Ty_bool
  | Ty_unit
  | Ty_id
  | Ty_sexp
  | Ty_arrow of ty list * ty

val int_ty : ty
val bool_ty : ty
val unit_ty : ty
val id_ty : ty
val sexp_ty : ty
val arrow : ty list -> ty -> ty
val equal_ty : ty -> ty -> bool

type op = Add | Sub | Mul | Eq | Lt

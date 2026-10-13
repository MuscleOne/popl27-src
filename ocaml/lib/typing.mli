(** Source typing, source-calculus.md section 6. This checks the source calculus
    itself, not the object-oriented language of the later application. Values
    and atoms use the term judgment restricted to those syntax classes. *)

open Syntax

type environment = ty Var.Map.t

type error =
  | Unbound_variable of Var.t
  | Type_mismatch of { rule : string; expected : ty; actual : ty }
  | Not_function of ty
  | Arity_mismatch of { expected : int; actual : int }
  | Equality_type of ty

exception Type_error of error

val type_value : environment -> value -> ty
val type_atom : environment -> atom -> ty
val type_term : environment -> term -> ty

val type_branch : environment -> branch -> ty
(** Return a type or raise [Type_error]. Function annotations are checked; no
    unification, subtyping, implicit coercion, or evaluation is performed. Use
    [Var.Map.empty] for checking a closed source term. *)

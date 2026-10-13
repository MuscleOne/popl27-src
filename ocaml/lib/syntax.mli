(** Source phrases, source-calculus.md sections 1--3. Bindlib represents
    variable binding. Private constructors enforce formation, not typing. *)
include
  module type of Common_syntax
    with type ty = Common_syntax.ty
     and type op = Common_syntax.op
     and type Id.t = Common_syntax.Id.t

(** Flat pattern head. Its field variables are held by the branch binder. *)
type pattern_head = P_int | P_bool | P_id | P_nil | P_pair | P_wildcard

type value = private
  | Integer of Z.t
  | Boolean of bool
  | Unit
  | Identifier of Id.t
  | Fun of ty list * ty * (atom, term) Bindlib.mbinder
  | Fix of ty list * ty * (atom, term) Bindlib.mbinder
  | Sexp_int of atom
  | Sexp_bool of atom
  | Sexp_id of atom
  | Nil
  | Pair of atom * atom

and atom = private Variable of atom Bindlib.var | Value of value

and term = private
  | Atom of atom
  | Apply of atom * atom list
  | Operation of atom * op * atom
  | If of atom * term * term
  | Let of term * (atom, term) Bindlib.binder
  | Match of atom * branch list
  | Async of term

and branch = private Branch of pattern_head * (atom, term) Bindlib.mbinder

type variable = atom Bindlib.var
type parameter = variable * ty

module Var : sig
  type t = variable

  val fresh : string -> t
  (** A fresh variable identity with a preferred display name. Two calls with
      the same string differ. Reuse one identity for a binder and its
      occurrences. *)

  val name : t -> string
  (** Preferred name only; use Print for capture-safe phrase display. *)

  val equal : t -> t -> bool
  val compare : t -> t -> int

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end

val integer : Z.t -> value
val boolean : bool -> value
val unit : value
val identifier : Id.t -> value
val fun_ : parameter list -> ty -> term -> value

val fix : variable -> parameter list -> ty -> term -> value
(** Fun binds parameters in order. Fix binds self first, then parameters; the
    stored type list excludes self. Constructors check nonempty parameters and
    distinct identities and recursively box the body. *)

val sexp_int : atom -> value
val sexp_bool : atom -> value
val sexp_id : atom -> value
val nil : value
val pair : atom -> atom -> value
val variable : variable -> atom
val value : value -> atom
val atom : atom -> term
val apply : atom -> atom list -> term
val operation : atom -> op -> atom -> term
val if_ : atom -> term -> term -> term
val let_ : variable -> term -> term -> term

val branch : pattern_head -> variable list -> term -> branch
(** Checks field count and distinct variables. Pair binds fields left-to-right;
    Nil and wildcard bind none. *)

val match_ : atom -> branch list -> term
val async : term -> term
val box_value : value -> value Bindlib.box
val box_atom : atom -> atom Bindlib.box
val box_term : term -> term Bindlib.box

val box_branch : branch -> branch Bindlib.box
(** Binding traversals: all free variables remain available for binding. Unlike
    Bindlib.box, these traverse open syntax correctly. *)

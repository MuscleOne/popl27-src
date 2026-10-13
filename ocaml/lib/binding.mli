open Syntax
(** Binding operations for source syntax modulo alpha equivalence:
    source-calculus.md, sections 4--5. None of these functions evaluates a
    source term. *)

val fv_value : value -> Var.Set.t
val fv_atom : atom -> Var.Set.t
val fv_term : term -> Var.Set.t
val fv_branch : branch -> Var.Set.t

val exchange_value : Var.t -> Var.t -> value -> value
(** Exchange of free identities represents the paper exchange modulo alpha
    equivalence. Identifier literals and types are fixed. *)

val exchange_atom : Var.t -> Var.t -> atom -> atom
val exchange_term : Var.t -> Var.t -> term -> term
val exchange_branch : Var.t -> Var.t -> branch -> branch

val alpha_equal_value : value -> value -> bool
(** Compare binders after opening both bodies at common fresh identities. Free
    identities, type annotations, constructor heads and sequence order must
    agree. *)

val alpha_equal_atom : atom -> atom -> bool
val alpha_equal_term : term -> term -> bool
val alpha_equal_branch : branch -> branch -> bool

type substitution

val empty : substitution
val single : Var.t -> atom -> substitution

val simultaneous : (Var.t * atom) list -> substitution
(** Input pairs are [(variable, replacement_atom)]. Duplicate variables raise
    [Invalid_argument]. *)

val subst_value : substitution -> value -> value
val subst_atom : substitution -> atom -> atom
val subst_term : substitution -> term -> term
val subst_branch : substitution -> branch -> branch

module S = Source_calculus.Syntax
(** The one-way conversion from source syntax to runtime syntax. Source and
    runtime have independent Bindlib variables and ASTs. Conversion opens each
    source binder and allocates corresponding runtime identities. No future
    allocation, type checking, normalization, or reduction occurs. *)

module R = Runtime_calculus.Runtime_syntax

type environment

val empty : environment

val add : S.Var.t -> R.variable -> environment -> environment
(** An injective association for free variables. Reusing one runtime variable
    for different source variables raises [Invalid_argument]. *)

exception Unbound_variable of S.Var.t

val value : ?free:environment -> S.value -> R.value
val atom : ?free:environment -> S.atom -> R.atom
val term : ?free:environment -> S.term -> R.term

val branch : ?free:environment -> S.branch -> R.branch
(** Defaults to closed input. Open phrases require explicit free-variable
    associations; reuse them when comparing several converted phrases. Missing
    associations raise Unbound_variable rather than inventing names. *)

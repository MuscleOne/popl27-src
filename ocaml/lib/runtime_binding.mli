open Runtime_syntax
(** Binding operations for runtime phrases: runtime-calculus.md, section 3. FV
    records source variables only. Substitution replaces source variables with
    runtime atoms and fixes future names; it does not dereference them. *)

val fv_value : value -> Var.Set.t
val fv_atom : atom -> Var.Set.t
val fv_term : term -> Var.Set.t
val fv_branch : branch -> Var.Set.t

val exchange_value : Var.t -> Var.t -> value -> value
(** Exchange of variable identities, interpreted modulo alpha-equivalence.
    Bindlib abstracts bound identities; exchanging the two free identities by
    simultaneous capture-avoiding substitution represents the paper exchange on
    alpha classes. It need not retain a particular binder display name. Futures,
    identifier literals and types are fixed. *)

val exchange_atom : Var.t -> Var.t -> atom -> atom
val exchange_term : Var.t -> Var.t -> term -> term
val exchange_branch : Var.t -> Var.t -> branch -> branch

val alpha_equal_value : value -> value -> bool
(** Bindlib compares binders using common fresh variables. Free source
    variables, exact future names, type annotations, constructor heads and
    sequence order must agree. *)

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
(** Replacements are inserted unchanged. These operations do not take an
    active-name set: to instantiate substitution on phrases at U, the subject
    and all replacement atoms must first be formed at that same U. *)

val subst_atom : substitution -> atom -> atom
val subst_term : substitution -> term -> term
val subst_branch : substitution -> branch -> branch

val exchange_future_value : FName.t -> FName.t -> value -> value
(** Exchange two future names throughout a phrase, fixing source variables,
    identifier literals and types. This transports formation from U to the
    exchanged active-name set; it need not preserve membership at the original
    U. This is only the phrase part of consistent state renaming, not an
    alpha-equivalence test on states. *)

val exchange_future_atom : FName.t -> FName.t -> atom -> atom
val exchange_future_term : FName.t -> FName.t -> term -> term
val exchange_future_branch : FName.t -> FName.t -> branch -> branch

open Runtime_syntax

type signature = ty FName.Map.t
type mapping = term FName.Map.t

type t = private { signature : signature; focus : term; mapping : mapping }
(** Formed displays nu Sigma { N || mu }, runtime-calculus.md sections 2.3--3.
    Only future scope and domain inclusion are enforced here. *)

exception Invalid_state of string

val make : signature -> term -> mapping -> t
(** Reject mapping keys or future occurrences outside the signature. Free
    source variables, ill-typed terms, missing entries and cycles are allowed. *)

val domain : 'a FName.Map.t -> FName.Set.t
val fresh : signature -> FName.t
(** Choose an unused name from the signature, without allocating or updating
    anything. This is one possible fresh-name choice, not a semantic rule. *)

val equal : t -> t -> bool
(** State-carrier equality: extensional maps, variable alpha-equivalence in
    terms, and exact future names. This does not identify future renamings. *)

val exchange_futures : FName.t -> FName.t -> t -> t
(** Consistently swap two future names in declarations, mapping keys and all
    phrases. This represents a transposition from section 3. *)

val final : t -> bool
(** State-Final, section 5: focus and all present entries are runtime values.
    Does not check State-Ok or follow aliases. *)

(** Sequential source reduction: source-calculus.md section 7. No runtime tasks,
    futures, scheduler, or implicit type checking. *)

type rule =
  | Search_let of rule
  | Beta
  | Fix_beta
  | Let
  | Src_async
  | Match_constructor
  | Match_wildcard
  | Add
  | Sub
  | Mul
  | Eq_int_true
  | Eq_int_false
  | Eq_id_true
  | Eq_id_false
  | Lt_true
  | Lt_false
  | If_true
  | If_false

val rule_name : rule -> string
(** The tag of the outermost rule. [Search_let inner] also records the rule used
    for the right-hand-side step, including further nested searches. These tags
    are diagnostic data, not additional source syntax. *)

val step : Syntax.term -> (rule * Syntax.term) option
(** One step on a named representative, or [None] when no rule applies. [None]
    does not assert that the input is a value, well typed, or closed. Search
    only descends through let right-hand sides, not within values or unselected
    branches. Substitution may choose fresh bound names; compare results modulo
    alpha. Iteration belongs to the caller, and need not terminate in the
    presence of [fix]. No iteration bound is part of this one-step relation. *)

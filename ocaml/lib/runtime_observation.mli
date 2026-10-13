(** Final-state observation, runtime-calculus.md section 8. This library bridges
    runtime states and source values; neither calculus core depends on it. *)

val unravel :
  Runtime_calculus.Runtime_state.mapping ->
  Runtime_calculus.Runtime_syntax.value ->
  Source_calculus.Syntax.value option
(** Section 8.2: [unravel mapping w = Some v] represents mu |- w ~> v. [None]
    means no finite unravelling derivation. No typing or finality check is
    imposed here. Only referenced entries are traversed, and only when they
    already contain values. Functions and source-variable fields have no rule.
    Cycles on the current path fail; repeated sharing is permitted. *)

val observe :
  Runtime_calculus.Runtime_state.t -> Source_calculus.Syntax.value option
(** Section 8.3, Unravel-State: check State-Ok, then State-Final, then unravel
    the focus. Return [Some v] for an observation, or [None] when any premise
    fails. [None] asserts neither deadlock nor divergence. Callers needing
    diagnostics can use [Runtime_calculus.Runtime_typing.check_state] and
    [Runtime_calculus.Runtime_state.final] separately.

    Neither operation evaluates a term, changes the mapping, or prints a result.
    Neither implements the more general readback used in metatheory.md. *)

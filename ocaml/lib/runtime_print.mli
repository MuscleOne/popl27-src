val ty : Format.formatter -> Runtime_syntax.ty -> unit
(** Phrase display with fresh variable names. Futures display as future(n), a
    diagnostic form, not additional source syntax. Non-lexical variable hints
    use var("...") diagnostics. No reduction is performed. *)

val value : Format.formatter -> Runtime_syntax.value -> unit
val atom : Format.formatter -> Runtime_syntax.atom -> unit
val term : Format.formatter -> Runtime_syntax.term -> unit
val branch : Format.formatter -> Runtime_syntax.branch -> unit

val state : Format.formatter -> Runtime_state.t -> unit
(** Diagnostic state display, with one variable naming context for the focus
    and every mapping entry. Future names are preserved. *)

val local_rule : Format.formatter -> Runtime_reduction.local_rule -> unit
val rule : Format.formatter -> Runtime_reduction.rule -> unit

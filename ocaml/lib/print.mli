(** Human-readable displays of the source syntax and its diagnostics.
    Parentheses delimit nested bodies; [=>] displays the branch separator.
    Identifier literals are quoted, not variables or a new string type. Unusual
    variable names are displayed as [var("...")]. These printers are not a
    parser or a serialization format. Binders are opened in a naming context;
    distinct free identities receive distinct display names. *)

val ty : Format.formatter -> Syntax.ty -> unit
val value : Format.formatter -> Syntax.value -> unit
val atom : Format.formatter -> Syntax.atom -> unit
val term : Format.formatter -> Syntax.term -> unit
val branch : Format.formatter -> Syntax.branch -> unit
val error : Format.formatter -> Typing.error -> unit

val rule : Format.formatter -> Reduction.rule -> unit
(** Include the inner rule when printing [Search_let]. *)

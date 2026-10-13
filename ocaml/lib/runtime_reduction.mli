(** Runtime-calculus.md sections 6--7. Rules retain their inner derivation. *)
type local_rule =
  | Search_let of local_rule
  | Beta
  | Fix_beta
  | Let
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
  | Spawn_async
  | Spawn_app
  | Deref_app_function
  | Deref_op_left
  | Deref_op_right
  | Deref_if_guard
  | Deref_match_scrutinee

type rule =
  | Interleave_focus of local_rule
  | Interleave_future of Runtime_syntax.FName.t * local_rule

val local_rule_name : local_rule -> string
val rule_name : rule -> string

val local_steps :
  fresh:Runtime_syntax.FName.t ->
  Runtime_state.t ->
  (local_rule * Runtime_state.t) list

val steps :
  fresh:Runtime_syntax.FName.t ->
  Runtime_state.t ->
  (rule * Runtime_state.t) list
(** Enumerate one-step successors for the supplied fresh name. [fresh] must lie
    outside the input signature (otherwise [Invalid_argument] is raised).
    [Runtime_state.fresh] supplies one such name. All allocation alternatives
    use that same name; other fresh-name instances are not enumerated.

    List order gives no semantic priority. Each result advances one position;
    neither function iterates or requires State-Ok. Self-loops are retained. An
    empty result alone asserts neither finality nor divergence. *)

open Runtime_syntax

type environment = ty Var.Map.t

type error =
  | Unbound_variable of Var.t
  | Unbound_future of FName.t
  | Type_mismatch of { rule : string; expected : ty; actual : ty }
  | Not_function of ty
  | Arity_mismatch of { expected : int; actual : int }
  | Equality_type of ty

exception Type_error of error

val type_value : Runtime_state.signature -> environment -> value -> ty
val type_atom : Runtime_state.signature -> environment -> atom -> ty
val type_term : Runtime_state.signature -> environment -> term -> ty

val type_branch : Runtime_state.signature -> environment -> branch -> ty
(** Runtime typing, section 4. Return the type or raise [Type_error]. Free
    source variables are looked up in Gamma, futures in Sigma. No mapping is
    consulted, and no evaluation, coercion or future type constructor is added.
    As in source Typing, every body/branch and function annotation is checked.
*)

type state_error =
  | Domain_mismatch
  | Focus_type_error of error
  | Entry_type_error of FName.t * error

exception State_error of state_error

val check_state : Runtime_state.t -> ty
(** State-Ok, section 5. Return the focus type if all three premises hold;
    otherwise raise [State_error]. Does not require finality or acyclicity. *)

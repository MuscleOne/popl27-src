(* runtime-calculus.md section 8. This bridge returns source values. *)
open Runtime_calculus
module R = Runtime_syntax
module S = Source_calculus.Syntax

let unravel mapping subject =
  (* A path, not a global visited set: two fields may share the same future.
     Revisiting a future on one path cannot have a finite derivation. *)
  let rec value path = function
    | R.Integer n -> Some (S.integer n)
    | R.Boolean b -> Some (S.boolean b)
    | R.Unit -> Some S.unit
    | R.Identifier id -> Some (S.identifier id)
    | R.Future p -> (
        if R.FName.Set.mem p path then None
        else
          match R.FName.Map.find_opt p mapping with
          | Some (R.Atom (R.Value w)) -> value (R.FName.Set.add p path) w
          | _ -> None)
    | R.Sexp_int a -> constructor path S.sexp_int a
    | R.Sexp_bool a -> constructor path S.sexp_bool a
    | R.Sexp_id a -> constructor path S.sexp_id a
    | R.Nil -> Some S.nil
    | R.Pair (a, b) -> (
        match atom path a with
        | None -> None
        | Some left ->
            Option.map
              (fun right -> S.pair (S.value left) (S.value right))
              (atom path b))
    | R.Fun _ | R.Fix _ -> None
  and atom path = function R.Value w -> value path w | R.Variable _ -> None
  and constructor path make field =
    Option.map (fun v -> make (S.value v)) (atom path field)
  in
  value R.FName.Set.empty subject

let observe state =
  match Runtime_typing.check_state state with
  | _ -> (
      if not (Runtime_state.final state) then None
      else
        match state.Runtime_state.focus with
        | R.Atom (R.Value w) -> unravel state.mapping w
        | _ -> None)
  | exception Runtime_typing.State_error _ -> None

(* runtime-calculus.md sections 2.3, 3 and 5. *)
open Runtime_syntax

type signature = ty FName.Map.t
type mapping = term FName.Map.t
type t = { signature : signature; focus : term; mapping : mapping }

exception Invalid_state of string

let domain entries =
  FName.Map.fold (fun p _ names -> FName.Set.add p names) entries FName.Set.empty

let make signature focus mapping =
  let active = domain signature in
  if not (FName.Set.subset (domain mapping) active) then
    raise (Invalid_state "Mapping domain is not contained in the signature");
  if not (formed_term active focus) then
    raise (Invalid_state "Focus contains an undeclared future");
  if not (FName.Map.for_all (fun _ body -> formed_term active body) mapping) then
    raise (Invalid_state "Mapping contains an undeclared future");
  { signature; focus; mapping }

let fresh signature =
  match FName.Map.max_binding_opt signature with
  | None -> FName.of_z Z.zero
  | Some (p, _) -> FName.of_z (Z.succ (FName.to_z p))

let equal left right =
  FName.Map.equal equal_ty left.signature right.signature
  && Runtime_binding.alpha_equal_term left.focus right.focus
  && FName.Map.equal Runtime_binding.alpha_equal_term left.mapping right.mapping

let exchange_futures p q state =
  let name r =
    if FName.equal r p then q else if FName.equal r q then p else r
  in
  let exchange_map image entries =
    FName.Map.fold
      (fun r item result -> FName.Map.add (name r) (image item) result)
      entries FName.Map.empty
  in
  let phrase = Runtime_binding.exchange_future_term p q in
  { signature = exchange_map (fun ty -> ty) state.signature;
    focus = phrase state.focus;
    mapping = exchange_map phrase state.mapping }

let final state =
  let is_value = function Atom (Value _) -> true | _ -> false in
  is_value state.focus && FName.Map.for_all (fun _ body -> is_value body) state.mapping

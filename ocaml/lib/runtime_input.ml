(* Representation conversion only: no normalization, typing, or evaluation. *)
module S = Source_calculus.Syntax
module R = Runtime_calculus.Runtime_syntax

type environment = R.variable S.Var.Map.t

let empty = S.Var.Map.empty

exception Unbound_variable of S.Var.t

let add x y env =
  if
    S.Var.Map.exists
      (fun other z -> (not (S.Var.equal x other)) && R.Var.equal y z)
      env
  then invalid_arg "Runtime_input.add: non-injective association";
  S.Var.Map.add x y env

let lookup env x =
  match S.Var.Map.find_opt x env with
  | Some y -> y
  | None -> raise (Unbound_variable x)

let bind env xs =
  let ys = List.map (fun x -> R.Var.fresh (S.Var.name x)) xs in
  let env = List.fold_left2 (fun env x y -> add x y env) env xs ys in
  (ys, env)

let rec value_in env = function
  | S.Integer n -> R.integer n
  | S.Boolean b -> R.boolean b
  | S.Unit -> R.unit
  | S.Identifier id -> R.identifier id
  | S.Fun (types, result, binding) ->
      let xs, body = Bindlib.unmbind binding in
      let ys, inner = bind env (Array.to_list xs) in
      R.fun_ (List.combine ys types) result (term_in inner body)
  | S.Fix (types, result, binding) -> (
      let xs, body = Bindlib.unmbind binding in
      let ys, inner = bind env (Array.to_list xs) in
      match ys with
      | self :: ys ->
          R.fix self (List.combine ys types) result (term_in inner body)
      | [] -> assert false)
  | S.Sexp_int a -> R.sexp_int (atom_in env a)
  | S.Sexp_bool a -> R.sexp_bool (atom_in env a)
  | S.Sexp_id a -> R.sexp_id (atom_in env a)
  | S.Nil -> R.nil
  | S.Pair (a, b) -> R.pair (atom_in env a) (atom_in env b)

and atom_in env = function
  | S.Variable x -> R.variable (lookup env x)
  | S.Value v -> R.value (value_in env v)

and term_in env = function
  | S.Atom a -> R.atom (atom_in env a)
  | S.Apply (fn, args) -> R.apply (atom_in env fn) (List.map (atom_in env) args)
  | S.Operation (a, op, b) -> R.operation (atom_in env a) op (atom_in env b)
  | S.If (g, y, n) -> R.if_ (atom_in env g) (term_in env y) (term_in env n)
  | S.Let (rhs, binding) ->
      let x, body = Bindlib.unbind binding in
      let y = R.Var.fresh (S.Var.name x) in
      R.let_ y (term_in env rhs) (term_in (add x y env) body)
  | S.Match (s, bs) -> R.match_ (atom_in env s) (List.map (branch_in env) bs)
  | S.Async body -> R.async (term_in env body)

and branch_in env (S.Branch (pat, binding)) =
  let xs, body = Bindlib.unmbind binding in
  let head =
    match pat with
    | S.P_int -> R.P_int
    | S.P_bool -> R.P_bool
    | S.P_id -> R.P_id
    | S.P_nil -> R.P_nil
    | S.P_pair -> R.P_pair
    | S.P_wildcard -> R.P_wildcard
  in
  let xs, inner = bind env (Array.to_list xs) in
  R.branch head xs (term_in inner body)

let value ?(free = empty) = value_in free
let atom ?(free = empty) = atom_in free
let term ?(free = empty) = term_in free
let branch ?(free = empty) = branch_in free

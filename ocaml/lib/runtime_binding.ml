(* runtime-calculus.md, section 3. Bindlib variables and explicit future names. *)
open Runtime_syntax
module Set = Var.Set
module Map = Var.Map

let union_list sets = List.fold_left Set.union Set.empty sets
let without xs fv = Array.fold_left (fun fv x -> Set.remove x fv) fv xs

let rec fv_value = function
  | Integer _ | Boolean _ | Unit | Identifier _ | Future _ | Nil -> Set.empty
  | Fun (_, _, body) | Fix (_, _, body) -> fv_body body
  | Sexp_int a | Sexp_bool a | Sexp_id a -> fv_atom a
  | Pair (a, b) -> Set.union (fv_atom a) (fv_atom b)

and fv_atom = function Variable x -> Set.singleton x | Value w -> fv_value w

and fv_term = function
  | Atom a -> fv_atom a
  | Apply (fn, args) -> union_list (List.map fv_atom (fn :: args))
  | Operation (a, _, b) -> Set.union (fv_atom a) (fv_atom b)
  | If (g, y, n) -> union_list [ fv_atom g; fv_term y; fv_term n ]
  | Let (rhs, body) ->
      let x, body = Bindlib.unbind body in
      Set.union (fv_term rhs) (Set.remove x (fv_term body))
  | Match (s, bs) -> Set.union (fv_atom s) (union_list (List.map fv_branch bs))
  | Async body -> fv_term body

and fv_branch (Branch (_, body)) = fv_body body

and fv_body body =
  let xs, body = Bindlib.unmbind body in
  without xs (fv_term body)

let equal_list equal xs ys =
  List.length xs = List.length ys && List.for_all2 equal xs ys

let rec alpha_equal_value a b =
  match (a, b) with
  | Integer n, Integer m -> Z.equal n m
  | Boolean b, Boolean c -> Bool.equal b c
  | Unit, Unit | Nil, Nil -> true
  | Identifier x, Identifier y -> Id.equal x y
  | Future p, Future q -> FName.equal p q
  | Fun (ts, t, body), Fun (us, u, other) | Fix (ts, t, body), Fix (us, u, other)
    ->
      equal_list equal_ty ts us && equal_ty t u
      && Bindlib.eq_mbinder alpha_equal_term body other
  | Sexp_int a, Sexp_int b | Sexp_bool a, Sexp_bool b | Sexp_id a, Sexp_id b ->
      alpha_equal_atom a b
  | Pair (a, b), Pair (c, d) -> alpha_equal_atom a c && alpha_equal_atom b d
  | _ -> false

and alpha_equal_atom a b =
  match (a, b) with
  | Variable x, Variable y -> Var.equal x y
  | Value w, Value v -> alpha_equal_value w v
  | _ -> false

and alpha_equal_term a b =
  match (a, b) with
  | Atom a, Atom b -> alpha_equal_atom a b
  | Apply (f, xs), Apply (g, ys) ->
      alpha_equal_atom f g && equal_list alpha_equal_atom xs ys
  | Operation (a, op, b), Operation (c, op', d) ->
      op = op' && alpha_equal_atom a c && alpha_equal_atom b d
  | If (g, y, n), If (h, a, b) ->
      alpha_equal_atom g h && alpha_equal_term y a && alpha_equal_term n b
  | Let (rhs, body), Let (rhs', body') ->
      alpha_equal_term rhs rhs' && Bindlib.eq_binder alpha_equal_term body body'
  | Match (s, bs), Match (t, cs) ->
      alpha_equal_atom s t && equal_list alpha_equal_branch bs cs
  | Async a, Async b -> alpha_equal_term a b
  | _ -> false

and alpha_equal_branch (Branch (p, body)) (Branch (q, other)) =
  p = q && Bindlib.eq_mbinder alpha_equal_term body other

type substitution = atom Map.t

let empty = Map.empty
let single = Map.singleton

let simultaneous entries =
  List.fold_left
    (fun subst (x, a) ->
      if Map.mem x subst then
        invalid_arg "Runtime_binding.simultaneous: duplicate variable";
      Map.add x a subst)
    empty entries

(* Bind all domain variables at once, then instantiate with unchanged atoms.
   Reboxing visits all open positions, including bodies of existing binders. *)
let substitute rebox subst phrase =
  if Map.is_empty subst then phrase
  else
    let xs, atoms = List.split (Map.bindings subst) in
    let body =
      Bindlib.unbox (Bindlib.bind_mvar (Array.of_list xs) (rebox phrase))
    in
    Bindlib.msubst body (Array.of_list atoms)

let subst_value = substitute box_value
let subst_atom = substitute box_atom
let subst_term = substitute box_term
let subst_branch = substitute box_branch

(* On alpha classes, simultaneous capture-avoiding exchange of the two free
   identities represents the paper exchange; bound display names are immaterial. *)
let exchange x y =
  if Var.equal x y then empty
  else simultaneous [ (x, variable y); (y, variable x) ]

let exchange_value x y = subst_value (exchange x y)
let exchange_atom x y = subst_atom (exchange x y)
let exchange_term x y = subst_term (exchange x y)
let exchange_branch x y = subst_branch (exchange x y)
let swap p q r = if FName.equal r p then q else if FName.equal r q then p else r

(* Future exchange is a separate traversal. Opening/reclosing variable binders
   does not use variable substitution to resolve or rename future names. *)
let rec rename_future_value rename = function
  | (Integer _ | Boolean _ | Unit | Identifier _ | Nil) as w -> w
  | Future p -> future (rename p)
  | Fun (types, result, body) ->
      let xs, body = Bindlib.unmbind body in
      fun_
        (List.combine (Array.to_list xs) types)
        result
        (rename_future_term rename body)
  | Fix (types, result, body) ->
      let xs, body = Bindlib.unmbind body in
      let self = xs.(0) in
      let params = Array.to_list (Array.sub xs 1 (Array.length xs - 1)) in
      fix self
        (List.combine params types)
        result
        (rename_future_term rename body)
  | Sexp_int a -> sexp_int (rename_future_atom rename a)
  | Sexp_bool a -> sexp_bool (rename_future_atom rename a)
  | Sexp_id a -> sexp_id (rename_future_atom rename a)
  | Pair (a, b) ->
      pair (rename_future_atom rename a) (rename_future_atom rename b)

and rename_future_atom rename = function
  | Variable x -> variable x
  | Value w -> value (rename_future_value rename w)

and rename_future_term rename = function
  | Atom a -> atom (rename_future_atom rename a)
  | Apply (fn, args) ->
      apply
        (rename_future_atom rename fn)
        (List.map (rename_future_atom rename) args)
  | Operation (a, op, b) ->
      operation (rename_future_atom rename a) op (rename_future_atom rename b)
  | If (g, y, n) ->
      if_
        (rename_future_atom rename g)
        (rename_future_term rename y)
        (rename_future_term rename n)
  | Let (rhs, body) ->
      let x, body = Bindlib.unbind body in
      let_ x (rename_future_term rename rhs) (rename_future_term rename body)
  | Match (s, bs) ->
      match_
        (rename_future_atom rename s)
        (List.map (rename_future_branch rename) bs)
  | Async body -> async (rename_future_term rename body)

and rename_future_branch rename (Branch (pat, body)) =
  let xs, body = Bindlib.unmbind body in
  branch pat (Array.to_list xs) (rename_future_term rename body)

let exchange_future_value p q = rename_future_value (swap p q)
let exchange_future_atom p q = rename_future_atom (swap p q)
let exchange_future_term p q = rename_future_term (swap p q)
let exchange_future_branch p q = rename_future_branch (swap p q)

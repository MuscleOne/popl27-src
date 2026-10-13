(* Named text -> variable identities, following Bindlib examples/parsed.ml.
   The free-name table belongs to one command; binders use lexical environments. *)
module P = Parsed_syntax
module S = Source_calculus.Syntax

let bind env names =
  if List.length (List.sort_uniq String.compare names) <> List.length names then
    raise (S.Invalid_syntax "Variables in one binder must be distinct");
  let xs = List.map S.Var.fresh names in
  (xs, List.combine names xs @ env)

let term ?(free = []) input =
  let names, variables = List.split free in
  if
    List.length (List.sort_uniq String.compare names) <> List.length names
    || S.Var.Set.cardinal (S.Var.Set.of_list variables) <> List.length variables
  then raise (S.Invalid_syntax "Free-name associations must be one-to-one");
  let free = ref free in
  let lookup env name =
    match List.assoc_opt name env with
    | Some x -> x
    | None -> (
        match List.assoc_opt name !free with
        | Some x -> x
        | None ->
            let x = S.Var.fresh name in
            free := (name, x) :: !free;
            x)
  in
  let rec value env = function
    | P.Integer n -> S.integer n
    | P.Boolean b -> S.boolean b
    | P.Unit -> S.unit
    | P.Identifier id -> S.identifier id
    | P.Fun (ps, result, body) ->
        let xs, inner = bind env (List.map fst ps) in
        S.fun_ (List.combine xs (List.map snd ps)) result (term inner body)
    | P.Fix (self, ps, result, body) -> (
        let xs, inner = bind env (self :: List.map fst ps) in
        match xs with
        | self :: xs ->
            S.fix self
              (List.combine xs (List.map snd ps))
              result (term inner body)
        | [] -> assert false)
    | P.Sexp_int a -> S.sexp_int (atom env a)
    | P.Sexp_bool a -> S.sexp_bool (atom env a)
    | P.Sexp_id a -> S.sexp_id (atom env a)
    | P.Nil -> S.nil
    | P.Pair (a, b) -> S.pair (atom env a) (atom env b)
  and atom env = function
    | P.Variable x -> S.variable (lookup env x)
    | P.Value v -> S.value (value env v)
  and term env = function
    | P.Atom a -> S.atom (atom env a)
    | P.Apply (fn, args) -> S.apply (atom env fn) (List.map (atom env) args)
    | P.Operation (a, op, b) -> S.operation (atom env a) op (atom env b)
    | P.If (g, y, n) -> S.if_ (atom env g) (term env y) (term env n)
    | P.Let (name, rhs, body) ->
        let x = S.Var.fresh name in
        S.let_ x (term env rhs) (term ((name, x) :: env) body)
    | P.Match (a, bs) -> S.match_ (atom env a) (List.map (branch env) bs)
    | P.Async body -> S.async (term env body)
  and branch env (P.Branch (pat, body)) =
    let head, names =
      match pat with
      | P.P_int x -> (S.P_int, [ x ])
      | P.P_bool x -> (S.P_bool, [ x ])
      | P.P_id x -> (S.P_id, [ x ])
      | P.P_nil -> (S.P_nil, [])
      | P.P_pair (x, y) -> (S.P_pair, [ x; y ])
      | P.P_wildcard -> (S.P_wildcard, [])
    in
    let xs, inner = bind env names in
    S.branch head xs (term inner body)
  in
  term [] input

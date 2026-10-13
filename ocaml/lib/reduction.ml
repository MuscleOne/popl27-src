(* source-calculus.md section 7. Each rule constructor names one displayed rule. *)
module S = Syntax

type rule =
  | Search_let of rule
  | Beta
  | Fix_beta
  | Let
  | Src_async
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

let rule_name = function
  | Search_let _ -> "Search-Let"
  | Beta -> "β"
  | Fix_beta -> "Fix-β"
  | Let -> "Let"
  | Src_async -> "Src-Async"
  | Match_constructor -> "Match-Constructor"
  | Match_wildcard -> "Match-Wildcard"
  | Add -> "Add"
  | Sub -> "Sub"
  | Mul -> "Mul"
  | Eq_int_true -> "Eq-Int-True"
  | Eq_int_false -> "Eq-Int-False"
  | Eq_id_true -> "Eq-Id-True"
  | Eq_id_false -> "Eq-Id-False"
  | Lt_true -> "Lt-True"
  | Lt_false -> "Lt-False"
  | If_true -> "If-True"
  | If_false -> "If-False"

let value_term v = S.atom (S.value v)
let integer_term n = value_term (S.integer n)
let boolean_term b = value_term (S.boolean b)

let value_arguments parameters arguments =
  List.length parameters = List.length arguments
  && List.for_all
       (function S.Value _ -> true | S.Variable _ -> false)
       arguments

(* Match-Constructor substitutes atom fields, not only value fields. *)
let match_fields constructor pattern =
  match (constructor, pattern) with
  | S.Sexp_int a, S.P_int | S.Sexp_bool a, S.P_bool | S.Sexp_id a, S.P_id ->
      Some [| a |]
  | S.Nil, S.P_nil -> Some [||]
  | S.Pair (a, b), S.P_pair -> Some [| a; b |]
  | _ -> None

(* The caller has checked that the scrutinee is a constructor value.
   Formation puts the unique wildcard last, so reaching it means that no
   constructor branch matched. No other kind of value selects the wildcard. *)
let rec select_branch constructor = function
  | S.Branch (S.P_wildcard, body) :: _ ->
      Some (Match_wildcard, Bindlib.msubst body [||])
  | S.Branch (pattern, body) :: rest -> (
      match match_fields constructor pattern with
      | Some replacements ->
          Some (Match_constructor, Bindlib.msubst body replacements)
      | None -> select_branch constructor rest)
  | [] -> None

let rec step : S.term -> (rule * S.term) option = function
  | S.Let (S.Atom (S.Value v), body) ->
      Some (Let, Bindlib.subst body (S.value v))
  | S.Let (rhs, binding) -> (
      match step rhs with
      | Some (rule, rhs') ->
          let x, body = Bindlib.unbind binding in
          Some (Search_let rule, S.let_ x rhs' body)
      | None -> None)
  | S.Apply (S.Value (S.Fun (types, _, body)), arguments)
    when value_arguments types arguments ->
      Some (Beta, Bindlib.msubst body (Array.of_list arguments))
  | S.Apply (S.Value (S.Fix (types, _, body) as recursive), arguments)
    when value_arguments types arguments ->
      Some
        ( Fix_beta,
          Bindlib.msubst body (Array.of_list (S.value recursive :: arguments))
        )
  | S.Async body -> Some (Src_async, body)
  | S.Match
      ( S.Value
          ((S.Sexp_int _ | S.Sexp_bool _ | S.Sexp_id _ | S.Nil | S.Pair _) as
           constructor),
        branches ) ->
      select_branch constructor branches
  | S.Operation (S.Value (S.Integer m), S.Add, S.Value (S.Integer n)) ->
      Some (Add, integer_term (Z.add m n))
  | S.Operation (S.Value (S.Integer m), S.Sub, S.Value (S.Integer n)) ->
      Some (Sub, integer_term (Z.sub m n))
  | S.Operation (S.Value (S.Integer m), S.Mul, S.Value (S.Integer n)) ->
      Some (Mul, integer_term (Z.mul m n))
  | S.Operation (S.Value (S.Integer m), S.Eq, S.Value (S.Integer n)) ->
      if Z.equal m n then Some (Eq_int_true, boolean_term true)
      else Some (Eq_int_false, boolean_term false)
  | S.Operation (S.Value (S.Identifier a), S.Eq, S.Value (S.Identifier b)) ->
      if S.Id.equal a b then Some (Eq_id_true, boolean_term true)
      else Some (Eq_id_false, boolean_term false)
  | S.Operation (S.Value (S.Integer m), S.Lt, S.Value (S.Integer n)) ->
      if Z.lt m n then Some (Lt_true, boolean_term true)
      else Some (Lt_false, boolean_term false)
  | S.If (S.Value (S.Boolean true), yes, _) -> Some (If_true, yes)
  | S.If (S.Value (S.Boolean false), _, no) -> Some (If_false, no)
  | S.Atom _ | S.Apply _ | S.Operation _ | S.If _ | S.Match _ -> None

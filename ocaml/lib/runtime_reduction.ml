(* runtime-calculus.md sections 6--7. One result per rule instance, for the
   supplied fresh name; the caller chooses among the alternatives. *)
module S = Runtime_syntax
module State = Runtime_state

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
  | Interleave_future of S.FName.t * local_rule

let local_rule_name = function
  | Search_let _ -> "Search-Let"
  | Beta -> "β"
  | Fix_beta -> "Fix-β"
  | Let -> "Let"
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
  | Spawn_async -> "Spawn-Async"
  | Spawn_app -> "Spawn-App"
  | Deref_app_function -> "Deref-App-Function"
  | Deref_op_left -> "Deref-Op-Left"
  | Deref_op_right -> "Deref-Op-Right"
  | Deref_if_guard -> "Deref-If-Guard"
  | Deref_match_scrutinee -> "Deref-Match-Scrutinee"

let rule_name = function
  | Interleave_focus _ -> "Interleave-Focus"
  | Interleave_future _ -> "Interleave-Future"

let value_term v = S.atom (S.value v)
let is_value = function S.Atom (S.Value _) -> true | _ -> false

let value_arguments parameters arguments =
  List.length parameters = List.length arguments
  && List.for_all
       (function S.Value _ -> true | S.Variable _ -> false)
       arguments

let rebind rhs binding =
  let x, body = Bindlib.unbind binding in
  S.let_ x rhs body

(* Exactly the trigger negated by Search-Let, without Spawn-App's typing
   premise. Only the displayed application atoms are inspected. *)
let needs_spawning mapping = function
  | S.Apply (fn, arguments) ->
      List.exists
        (function
          | S.Value (S.Future p) -> (
              match S.FName.Map.find_opt p mapping with
              | Some body -> not (is_value body)
              | None -> false)
          | _ -> false)
        (fn :: arguments)
  | _ -> false

let match_fields constructor pattern =
  match (constructor, pattern) with
  | S.Sexp_int a, S.P_int | S.Sexp_bool a, S.P_bool | S.Sexp_id a, S.P_id ->
      Some [| a |]
  | S.Nil, S.P_nil -> Some [||]
  | S.Pair (a, b), S.P_pair -> Some [| a; b |]
  | _ -> None

(* Called only for a constructor value. Formation puts the wildcard last. *)
let rec select_branch constructor = function
  | S.Branch (S.P_wildcard, body) :: _ ->
      [ (Match_wildcard, Bindlib.msubst body [||]) ]
  | S.Branch (pattern, body) :: rest -> (
      match match_fields constructor pattern with
      | Some fields -> [ (Match_constructor, Bindlib.msubst body fields) ]
      | None -> select_branch constructor rest)
  | [] -> []

let local_steps ~fresh state =
  if S.FName.Map.mem fresh state.State.signature then
    invalid_arg "Runtime_reduction.local_steps: name is not fresh";
  (* Search-Let descends into the focus with the same signature and mapping. *)
  let rec local focus =
    let unchanged rule focus =
      [ (rule, State.make state.State.signature focus state.mapping) ]
    in
    let spawn rule body continuation =
      match Runtime_typing.type_term state.signature S.Var.Map.empty body with
      | annotation ->
          [
            ( rule,
              State.make
                (S.FName.Map.add fresh annotation state.signature)
                (continuation (value_term (S.future fresh)))
                (S.FName.Map.add fresh body state.mapping) );
          ]
      | exception Runtime_typing.Type_error _ -> []
    in
    let dereference rule argument rebuild =
      match argument with
      | S.Value (S.Future p) -> (
          match S.FName.Map.find_opt p state.mapping with
          | Some (S.Atom (S.Value w)) -> unchanged rule (rebuild (S.value w))
          | _ -> [])
      | _ -> []
    in
    match focus with
    | S.Let (S.Atom (S.Value v), body) ->
        unchanged Let (Bindlib.subst body (S.value v))
    | S.Let (rhs, binding) ->
        if needs_spawning state.mapping rhs then
          spawn Spawn_app rhs (fun rhs -> rebind rhs binding)
        else
          local rhs
          |> List.map (fun (rule, next) ->
              ( Search_let rule,
                State.make next.State.signature
                  (rebind next.focus binding)
                  next.mapping ))
    | S.Apply (S.Value (S.Fun (types, _, body)), arguments)
      when value_arguments types arguments ->
        unchanged Beta (Bindlib.msubst body (Array.of_list arguments))
    | S.Apply (S.Value (S.Fix (types, _, body) as recursive), arguments)
      when value_arguments types arguments ->
        unchanged Fix_beta
          (Bindlib.msubst body (Array.of_list (S.value recursive :: arguments)))
    | S.Apply (fn, arguments) ->
        dereference Deref_app_function fn (fun fn -> S.apply fn arguments)
    | S.Async body -> spawn Spawn_async body (fun name -> name)
    | S.Match
        ( S.Value
            ((S.Sexp_int _ | S.Sexp_bool _ | S.Sexp_id _ | S.Nil | S.Pair _) as
             constructor),
          branches ) ->
        select_branch constructor branches
        |> List.map (fun (rule, focus) ->
            (rule, State.make state.signature focus state.mapping))
    | S.Match (scrutinee, branches) ->
        dereference Deref_match_scrutinee scrutinee (fun a ->
            S.match_ a branches)
    | S.Operation (S.Value (S.Integer m), S.Add, S.Value (S.Integer n)) ->
        unchanged Add (value_term (S.integer (Z.add m n)))
    | S.Operation (S.Value (S.Integer m), S.Sub, S.Value (S.Integer n)) ->
        unchanged Sub (value_term (S.integer (Z.sub m n)))
    | S.Operation (S.Value (S.Integer m), S.Mul, S.Value (S.Integer n)) ->
        unchanged Mul (value_term (S.integer (Z.mul m n)))
    | S.Operation (S.Value (S.Integer m), S.Eq, S.Value (S.Integer n)) ->
        if Z.equal m n then unchanged Eq_int_true (value_term (S.boolean true))
        else unchanged Eq_int_false (value_term (S.boolean false))
    | S.Operation (S.Value (S.Identifier a), S.Eq, S.Value (S.Identifier b)) ->
        if S.Id.equal a b then
          unchanged Eq_id_true (value_term (S.boolean true))
        else unchanged Eq_id_false (value_term (S.boolean false))
    | S.Operation (S.Value (S.Integer m), S.Lt, S.Value (S.Integer n)) ->
        if Z.lt m n then unchanged Lt_true (value_term (S.boolean true))
        else unchanged Lt_false (value_term (S.boolean false))
    | S.Operation (left, op, right) ->
        dereference Deref_op_left left (fun a -> S.operation a op right)
        @ dereference Deref_op_right right (fun a -> S.operation left op a)
    | S.If (S.Value (S.Boolean true), yes, _) -> unchanged If_true yes
    | S.If (S.Value (S.Boolean false), _, no) -> unchanged If_false no
    | S.If (guard, yes, no) ->
        dereference Deref_if_guard guard (fun a -> S.if_ a yes no)
    | S.Atom _ -> []
  in
  local state.State.focus

let steps ~fresh state =
  let focus_steps =
    local_steps ~fresh state
    |> List.map (fun (rule, next) -> (Interleave_focus rule, next))
  in
  let future_steps =
    S.FName.Map.bindings state.State.mapping
    |> List.concat_map (fun (p, body) ->
        local_steps ~fresh (State.make state.signature body state.mapping)
        |> List.map (fun (rule, next) ->
            (* Write into mu', retaining any allocation from the local step. *)
            ( Interleave_future (p, rule),
              State.make next.State.signature state.focus
                (S.FName.Map.add p next.focus next.mapping) )))
  in
  focus_steps @ future_steps

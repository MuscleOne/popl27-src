open Runtime_calculus
open Runtime_syntax
module State = Runtime_state
module R = Runtime_reduction

let check label condition = if not condition then failwith label
let empty = FName.Map.empty
let p = FName.of_z Z.zero
let q = FName.of_z Z.one
let r = FName.of_z (Z.of_int 2)
let x = Var.fresh "x"
let y = Var.fresh "y"
let f = Var.fresh "f"
let int n = value (integer (Z.of_int n))
let bool b = value (boolean b)
let id s = value (identifier (Id.of_string s))
let name p = value (future p)
let number n = atom (int n)
let sum = operation (int 1) Add (int 2)
let state focus = State.make empty focus empty
let same = Runtime_binding.alpha_equal_term
let local s = R.local_steps ~fresh:(State.fresh s.State.signature) s
let steps s = R.steps ~fresh:(State.fresh s.State.signature) s

let only rule expected = function
  | [ (actual, target) ] ->
      check (R.local_rule_name rule)
        (actual = rule && State.equal target expected)
  | _ -> failwith (R.local_rule_name rule ^ ": expected one successor")

let inherited_rules () =
  List.iter
    (fun (rule, input, output) ->
      only rule (state output) (local (state input)))
    [
      (R.Add, sum, number 3);
      (R.Sub, operation (int 1) Sub (int 2), number (-1));
      (R.Mul, operation (int 3) Mul (int 2), number 6);
      (R.Eq_int_true, operation (int 2) Eq (int 2), atom (bool true));
      (R.Eq_int_false, operation (int 1) Eq (int 2), atom (bool false));
      (R.Eq_id_true, operation (id "a") Eq (id "a"), atom (bool true));
      (R.Eq_id_false, operation (id "a") Eq (id "b"), atom (bool false));
      (R.Lt_true, operation (int 1) Lt (int 2), atom (bool true));
      (R.Lt_false, operation (int 2) Lt (int 1), atom (bool false));
      (R.If_true, if_ (bool true) (number 1) (number 2), number 1);
      (R.If_false, if_ (bool false) (number 1) (number 2), number 2);
      (R.Let, let_ x (number 1) (atom (variable x)), number 1);
      ( R.Beta,
        apply
          (value (fun_ [ (x, int_ty) ] int_ty (atom (variable x))))
          [ int 1 ],
        number 1 );
      ( R.Search_let R.Add,
        let_ x sum (atom (variable x)),
        let_ x (number 3) (atom (variable x)) );
    ];
  let recursive =
    value (fix f [ (x, int_ty) ] int_ty (apply (variable f) [ variable x ]))
  in
  (* Fix-beta substitutes both self and the argument, without iterating. *)
  let call = apply recursive [ int 1 ] in
  only R.Fix_beta (state call) (local (state call));
  List.iter
    (fun (constructor, head, fields, body, expected) ->
      let cases =
        [ branch head fields body; branch P_wildcard [] (number 9) ]
      in
      only R.Match_constructor (state expected)
        (local (state (match_ (value constructor) cases))))
    [
      (sexp_int (int 1), P_int, [ x ], atom (variable x), number 1);
      (sexp_bool (bool true), P_bool, [ x ], atom (variable x), atom (bool true));
      (sexp_id (id "a"), P_id, [ x ], atom (variable x), atom (id "a"));
      (nil, P_nil, [], number 1, number 1);
      ( pair (variable y) (value nil),
        P_pair,
        [ x; f ],
        atom (variable x),
        atom (variable y) );
    ];
  let cases = [ branch P_nil [] (number 1); branch P_wildcard [] (number 9) ] in
  only R.Match_wildcard
    (state (number 9))
    (local (state (match_ (value (sexp_int (int 1))) cases)));
  List.iter
    (fun term -> check "no inherited rule" (local (state term) = []))
    [
      match_ (int 1) cases;
      operation (bool true) Eq (bool true);
      atom (value (fun_ [ (x, int_ty) ] int_ty sum));
      apply (value (fun_ [ (x, int_ty) ] int_ty sum)) [ variable y ];
      apply (value (fun_ [ (x, int_ty) ] int_ty sum)) [ int 1; int 2 ];
    ]

let spawning () =
  let signature = FName.Map.singleton p int_ty in
  let mapping = FName.Map.singleton p sum in
  let make focus = State.make signature focus mapping in
  let identity = value (fun_ [ (x, int_ty) ] int_ty (atom (variable x))) in
  let call = apply identity [ name p ] in
  let bind rhs = let_ y rhs (atom (variable y)) in
  only R.Beta (make (atom (name p))) (local (make call));
  only R.Let (make (atom (name p))) (local (make (bind (atom (name p)))));
  let spawned =
    State.make
      (FName.Map.add q int_ty signature)
      (bind (atom (name q)))
      (FName.Map.add q call mapping)
  in
  only R.Spawn_app spawned (local (make (bind call)));
  let ignores = value (fun_ [ (x, int_ty) ] int_ty (number 7)) in
  let bad_call = apply ignores [ name p; name p ] in
  check "spawn typing failure does not fall back to Search-Let"
    (local (make (bind bad_call)) = []);
  let wrong_type =
    apply (value (fun_ [ (x, bool_ty) ] int_ty (number 7))) [ name p ]
  in
  only R.Beta (make (number 7)) (local (make wrong_type));
  check "exact negative premise despite possible beta"
    (local (make (bind wrong_type)) = []);
  let two =
    apply
      (value (fun_ [ (x, int_ty); (y, int_ty) ] int_ty (number 7)))
      [ name p; name p ]
  in
  only R.Spawn_app
    (State.make
       (FName.Map.add q int_ty signature)
       (bind (atom (name q)))
       (FName.Map.add q two mapping))
    (local (make (bind two)));
  let fn_signature = FName.Map.singleton p (arrow [ int_ty ] int_ty) in
  let fn_mapping = FName.Map.singleton p (async (atom identity)) in
  let fn_call = apply (name p) [ int 1 ] in
  only R.Spawn_app
    (State.make
       (FName.Map.add q int_ty fn_signature)
       (bind (atom (name q)))
       (FName.Map.add q fn_call fn_mapping))
    (local (State.make fn_signature (bind fn_call) fn_mapping));
  let missing = State.make signature (bind call) empty in
  only (R.Search_let R.Beta)
    (State.make signature (bind (atom (name p))) empty)
    (local missing);
  let alias_map = FName.Map.singleton p (atom (name p)) in
  only (R.Search_let R.Beta)
    (State.make signature (bind (atom (name p))) alias_map)
    (local (State.make signature (bind call) alias_map));
  let nested = apply ignores [ value (pair (name p) (value nil)) ] in
  only (R.Search_let R.Beta)
    (make (bind (number 7)))
    (local (make (bind nested)));
  only R.Spawn_async
    (State.make signature (atom (name p)) mapping)
    (local (state (async sum)));
  only (R.Search_let R.Spawn_async)
    (State.make signature (bind (atom (name p))) mapping)
    (local (state (bind (async sum))));
  List.iter
    (fun body ->
      check "spawn needs empty-environment typing"
        (local (state (async body)) = []))
    [ atom (variable x); operation (bool true) Add (int 1) ];
  let allocated_with_r =
    State.make
      (FName.Map.singleton r int_ty)
      (atom (name r))
      (FName.Map.singleton r sum)
  in
  only R.Spawn_async allocated_with_r
    (R.local_steps ~fresh:r (state (async sum)));
  check "fresh choices correspond by exchange"
    (State.equal allocated_with_r
       (State.exchange_futures p r
          (State.make signature (atom (name p)) mapping)));
  match R.local_steps ~fresh:p (make (number 0)) with
  | _ -> failwith "nonfresh name accepted"
  | exception Invalid_argument _ -> ()

let dereferencing () =
  let signature = FName.Map.(empty |> add p int_ty |> add q int_ty) in
  let mapping =
    FName.Map.(empty |> add p (atom (name q)) |> add q (number 3))
  in
  let make focus = State.make signature focus mapping in
  let cases = [ branch P_nil [] (number 0); branch P_wildcard [] (number 1) ] in
  (* Dereferencing has no typing premise and takes one alias hop only. *)
  List.iter
    (fun (rule, input, output) -> only rule (make output) (local (make input)))
    [
      (R.Deref_app_function, apply (name p) [ int 1 ], apply (name q) [ int 1 ]);
      ( R.Deref_op_left,
        operation (name p) Add (int 1),
        operation (name q) Add (int 1) );
      ( R.Deref_op_right,
        operation (int 1) Add (name p),
        operation (int 1) Add (name q) );
      ( R.Deref_if_guard,
        if_ (name p) (number 1) (number 2),
        if_ (name q) (number 1) (number 2) );
      (R.Deref_match_scrutinee, match_ (name p) cases, match_ (name q) cases);
    ];
  let choices = local (make (operation (name p) Add (name p))) in
  check "both operands, one occurrence per step"
    (List.length choices = 2
    && List.exists
         (fun (rule, s) ->
           rule = R.Deref_op_left
           && same s.State.focus (operation (name q) Add (name p)))
         choices
    && List.exists
         (fun (rule, s) ->
           rule = R.Deref_op_right
           && same s.State.focus (operation (name p) Add (name q)))
         choices);
  let loop =
    State.make signature
      (operation (name p) Add (int 1))
      (FName.Map.singleton p (atom (name p)))
  in
  only R.Deref_op_left loop (local loop);
  List.iter
    (fun term -> check "no eager dereference" (local (make term) = []))
    [
      atom (name p);
      atom (value (pair (name p) (name p)));
      apply (variable f) [ name p ];
    ];
  List.iter
    (fun entries ->
      check "no value available"
        (local (State.make signature (operation (name p) Add (int 1)) entries)
        = []))
    [ empty; FName.Map.singleton p sum ]

let interleaving () =
  let signature = FName.Map.(empty |> add p int_ty |> add q int_ty) in
  let mapping = FName.Map.(empty |> add p (async sum) |> add q sum) in
  let initial = State.make signature sum mapping in
  let choices = steps initial in
  let expected =
    [
      (R.Interleave_focus R.Add, State.make signature (number 3) mapping);
      ( R.Interleave_future (p, R.Spawn_async),
        State.make
          (FName.Map.add r int_ty signature)
          sum
          FName.Map.(mapping |> add r sum |> add p (atom (name r))) );
      ( R.Interleave_future (q, R.Add),
        State.make signature sum (FName.Map.add q (number 3) mapping) );
    ]
  in
  check "all positions; write back into the extended mapping; one step only"
    (List.length choices = 3
    && List.for_all
         (fun (rule, s) ->
           List.exists
             (fun (actual, t) -> rule = actual && State.equal s t)
             choices)
         expected);
  check "nested rule display"
    (Format.asprintf "%a" Runtime_print.rule
       (R.Interleave_future (p, R.Search_let R.Spawn_async))
    = "Interleave-Future(future(0), Search-Let(Spawn-Async))");
  check "stuck does not imply final"
    (let s = state (operation (bool true) Add (int 1)) in
     steps s = [] && not (State.final s))

let source_executions () =
  (* Exhaust the finite reachable graph of these examples using one fresh-name
     choice. This checks intermediate states, not a general preservation claim. *)
  List.iter
    (fun (text, answer) ->
      let source =
        match Source_frontend.Frontend.toplevel (Lexing.from_string text) with
        | Ok command -> command.Zoo.data
        | Error (_, message) -> failwith message
      in
      let initial = state (Runtime_input.term source) in
      let expected_type = Runtime_typing.check_state initial in
      let rec visit seen finals = function
        | [] -> check "example reaches a final state" (finals > 0)
        | (depth, s) :: rest ->
            if List.exists (State.equal s) seen then visit seen finals rest
            else (
              check "finite example depth" (depth < 30);
              check "State-Ok and focus type at every reached state"
                (equal_ty (Runtime_typing.check_state s) expected_type);
              let next = steps s in
              if next = [] then
                check text (State.final s && same s.focus (number answer));
              visit (s :: seen)
                (if next = [] then finals + 1 else finals)
                (rest @ List.map (fun (_, t) -> (depth + 1, t)) next))
      in
      visit [] 0 [ (0, initial) ])
    [
      ("let x = async (1 + 2) in x + x", 6);
      ( "let inc = fun (x : int) : int is x + 1 in let p = async (1 + 2) in \
         let r = inc(p) in r + 1",
        5 );
      ("let p = async (1 + 2) in match Int(p) { Int(x) => x + 1 | _ => 0 }", 4);
    ]

let () =
  inherited_rules ();
  spawning ();
  dereferencing ();
  interleaving ();
  source_executions ();
  print_endline "Runtime local/interleaving reduction checks passed"

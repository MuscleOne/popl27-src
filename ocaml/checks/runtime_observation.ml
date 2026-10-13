open Runtime_calculus
open Runtime_syntax
module State = Runtime_state
module O = Runtime_observation
module S = Source_calculus.Syntax

let check label condition = if not condition then failwith label
let empty = FName.Map.empty
let p = FName.of_z Z.zero
let q = FName.of_z Z.one
let r = FName.of_z (Z.of_int 2)
let x = Var.fresh "x"
let f = Var.fresh "f"
let term w = atom (value w)
let int n = integer (Z.of_int n)
let source_int n = S.integer (Z.of_int n)
let sexp n = sexp_int (value (int n))
let source_sexp n = S.sexp_int (S.value (source_int n))
let same = Source_calculus.Binding.alpha_equal_value

let expect_value label expected = function
  | Some actual -> check label (same actual expected)
  | None -> failwith (label ^ ": no unravelling")

let expect_observation label expected state =
  match O.observe state with
  | Some actual -> check label (same actual expected)
  | None -> failwith (label ^ ": no observation")

let auxiliary_rules () =
  let id = Id.of_string "ClassName" in
  List.iter
    (fun (input, expected) ->
      expect_value "primitive/constructor unravelling" expected
        (O.unravel empty input))
    [
      (int 21, source_int 21);
      (boolean true, S.boolean true);
      (boolean false, S.boolean false);
      (unit, S.unit);
      (identifier id, S.identifier id);
      (sexp 21, source_sexp 21);
      (sexp_bool (value (boolean true)), S.sexp_bool (S.value (S.boolean true)));
      (sexp_id (value (identifier id)), S.sexp_id (S.value (S.identifier id)));
      (nil, S.nil);
      ( pair (value (sexp 21)) (value nil),
        S.pair (S.value (source_sexp 21)) (S.value S.nil) );
    ];
  let mapping =
    FName.Map.(empty |> add p (term (future q)) |> add q (term (sexp 21)))
  in
  expect_value "alias chain" (source_sexp 21) (O.unravel mapping (future p));
  expect_value "shared future in both fields"
    (S.pair (S.value (source_sexp 21)) (S.value (source_sexp 21)))
    (O.unravel mapping (pair (value (future p)) (value (future p))));
  check "no path compression"
    (Runtime_binding.alpha_equal_term (FName.Map.find p mapping)
       (term (future q)));
  (* The auxiliary judgment has no typing premise. *)
  expect_value "untyped constructor still unravels"
    (S.sexp_int (S.value (S.boolean true)))
    (O.unravel empty (sexp_int (value (boolean true))));
  let pending = operation (value (int 1)) Add (value (int 2)) in
  let entries = FName.Map.singleton p pending in
  expect_value "unrelated pending entry is ignored" (source_int 21)
    (O.unravel entries (int 21));
  check "a referenced computation is not evaluated"
    (O.unravel entries (future p) = None);
  check "pending entry retained"
    (Runtime_binding.alpha_equal_term (FName.Map.find p entries) pending);
  List.iter
    (fun w -> check "no auxiliary rule" (O.unravel empty w = None))
    [
      future p;
      sexp_int (variable x);
      pair (value nil) (variable x);
      fun_ [ (x, int_ty) ] int_ty (atom (variable x));
      fix f [ (x, int_ty) ] int_ty (atom (variable x));
    ];
  List.iter
    (fun entries ->
      check "no finite cyclic unravelling" (O.unravel entries (future p) = None))
    [
      FName.Map.singleton p (term (future p));
      FName.Map.(empty |> add p (term (future q)) |> add q (term (future p)));
      FName.Map.singleton p (term (pair (value nil) (value (future p))));
    ]

let state_premises () =
  let signature = FName.Map.(empty |> add p sexp_ty |> add q sexp_ty) in
  let mapping =
    FName.Map.(empty |> add p (term (sexp 21)) |> add q (term (future q)))
  in
  let focus = term (pair (value (future p)) (value (future p))) in
  let state = State.make signature focus mapping in
  let expected = S.pair (S.value (source_sexp 21)) (S.value (source_sexp 21)) in
  expect_observation "unrelated alias cycle permits observation" expected state;
  expect_observation "consistent future renaming" expected
    (State.exchange_futures p r state);
  check "observation leaves state intact"
    (State.equal state (State.make signature focus mapping));
  let missing = State.make signature focus (FName.Map.remove q mapping) in
  check "final does not imply ok" (State.final missing);
  check "domain equality is required by observation" (O.observe missing = None);
  let wrong_type =
    State.make
      (FName.Map.singleton p int_ty)
      (term (int 21))
      (FName.Map.singleton p (term (boolean true)))
  in
  check "unrelated entry must still typecheck" (O.observe wrong_type = None);
  let open_focus = State.make empty (term (sexp_int (variable x))) empty in
  check "focus must typecheck in empty Gamma" (O.observe open_focus = None);
  let pending =
    State.make
      (FName.Map.singleton p int_ty)
      (term (int 21))
      (FName.Map.singleton p (async (term (int 1))))
  in
  check "all entries must be final" (O.observe pending = None);
  check "focus must be final"
    (O.observe (State.make empty (async (term (int 21))) empty) = None);
  let cyclic = State.make signature (term (future q)) mapping in
  check "ok final cycle lacks observation" (O.observe cyclic = None);
  List.iter
    (fun fn ->
      check "ok final function lacks observation"
        (O.observe (State.make empty (term fn) empty) = None))
    [
      fun_ [ (x, int_ty) ] int_ty (atom (variable x));
      fix f [ (x, int_ty) ] int_ty (atom (variable x));
    ]

let source_executions () =
  (* One finite path per example. Choosing the first successor here is only a
     check driver, not a scheduler exported by the runtime. *)
  let rec source_run fuel body =
    check "source example budget" (fuel > 0);
    match Source_calculus.Reduction.step body with
    | Some (_, next) -> source_run (fuel - 1) next
    | None -> (
        match body with S.Atom (S.Value v) -> v | _ -> failwith "source stuck")
  in
  let rec runtime_run fuel state =
    check "runtime example budget" (fuel > 0);
    if State.final state then state
    else
      match
        Runtime_reduction.steps ~fresh:(State.fresh state.State.signature) state
      with
      | (_, next) :: _ -> runtime_run (fuel - 1) next
      | [] -> failwith "runtime stuck"
  in
  List.iter
    (fun text ->
      let source =
        match Source_frontend.Frontend.toplevel (Lexing.from_string text) with
        | Ok command -> command.Zoo.data
        | Error (_, message) -> failwith message
      in
      let final =
        runtime_run 100 (State.make empty (Runtime_input.term source) empty)
      in
      expect_observation text (source_run 100 source) final)
    [
      "let x = async 21 in x";
      "let p = async (Int(21)) in Pair(p, p)";
      "let inc = fun (x : int) : int is x + 1 in let p = async (20 + 1) in let \
       r = inc(p) in r + 1";
    ]

let () =
  auxiliary_rules ();
  state_premises ();
  source_executions ();
  print_endline
    "Runtime value unravelling and final-state observation checks passed"

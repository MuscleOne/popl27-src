(* Concrete instances of source-calculus.md section 7, including open and
   ill-typed terms where the reduction relation is still defined. *)
open Source_calculus.Syntax
module B = Source_calculus.Binding
module R = Source_calculus.Reduction
module T = Source_calculus.Typing

let x = Var.fresh "x"
let y = Var.fresh "y"
let z = Var.fresh "z"
let f = Var.fresh "f"
let a = variable
let t x = atom (a x)
let int n = value (integer (Z.of_int n))
let bool b = value (boolean b)
let id s = value (identifier (Id.of_string s))
let nil_atom = value nil
let pair_term left right = atom (value (pair left right))
let check label condition = if not condition then failwith label

let expect_step label expected_rule input expected =
  match R.step input with
  | Some (rule, actual) ->
      check (label ^ ": rule") (rule = expected_rule);
      check (label ^ ": successor") (B.alpha_equal_term actual expected)
  | None -> failwith (label ^ ": missing step")

let no_step label input =
  match R.step input with
  | None -> ()
  | Some _ -> failwith (label ^ ": unexpected step")

let primitives () =
  List.iter
    (fun (rule, input, expected) ->
      expect_step (R.rule_name rule) rule input expected)
    [
      (R.Add, operation (int 2) Add (int 3), atom (int 5));
      (R.Sub, operation (int 3) Sub (int 5), atom (int (-2)));
      (R.Mul, operation (int (-3)) Mul (int 5), atom (int (-15)));
      (R.Eq_int_true, operation (int 3) Eq (int 3), atom (bool true));
      (R.Eq_int_false, operation (int 3) Eq (int 5), atom (bool false));
      (R.Eq_id_true, operation (id "class") Eq (id "class"), atom (bool true));
      (R.Eq_id_false, operation (id "class") Eq (id "Class"), atom (bool false));
      (R.Lt_true, operation (int (-1)) Lt (int 0), atom (bool true));
      (R.Lt_false, operation (int 3) Lt (int 3), atom (bool false));
    ];
  let huge = Z.of_string "184467440737095516160000000000000000001" in
  expect_step "unbounded addition" R.Add
    (operation (value (integer huge)) Add (int 1))
    (atom (value (integer (Z.succ huge))))

let application () =
  let choose =
    fun_ [ (x, bool_ty); (y, int_ty) ] int_ty (if_ (a x) (t y) (atom (int 0)))
  in
  expect_step "beta only substitutes" R.Beta
    (apply (value choose) [ bool true; int 7 ])
    (if_ (bool true) (atom (int 7)) (atom (int 0)));
  let fn =
    fun_ [ (x, sexp_ty); (y, sexp_ty) ] sexp_ty (pair_term (a x) (a y))
  in
  let open_value = value (sexp_int (a y)) in
  expect_step "beta replacements are simultaneous" R.Beta
    (apply (value fn) [ open_value; nil_atom ])
    (pair_term open_value nil_atom);
  let inner = fun_ [ (y, sexp_ty) ] sexp_ty (pair_term (a x) (a y)) in
  let outer =
    fun_ [ (x, sexp_ty) ] (arrow [ sexp_ty ] sexp_ty) (atom (value inner))
  in
  expect_step "beta avoids capture" R.Beta
    (apply (value outer) [ open_value ])
    (atom (value (fun_ [ (z, sexp_ty) ] sexp_ty (pair_term open_value (a z)))));
  no_step "beta needs values, not variable atoms"
    (apply (value choose) [ a x; int 7 ]);
  no_step "arity must agree" (apply (value choose) [ bool true ]);
  no_step "function position must be a function" (apply (int 1) [ int 2 ]);
  (* Typing is not a premise of beta. *)
  expect_step "beta does not call the typechecker" R.Beta
    (apply (value (fun_ [ (x, int_ty) ] int_ty (t x))) [ bool true ])
    (atom (bool true));
  let recursive = fix f [ (x, int_ty) ] int_ty (apply (a f) [ a x ]) in
  let call = apply (value recursive) [ int 1 ] in
  expect_step "fix inserts its own value without evaluating it" R.Fix_beta call
    call

let search_and_let () =
  let addition = operation (int 1) Add (int 2) in
  let body = operation (a x) Add (int 3) in
  let nested = let_ x (let_ y (async addition) (t y)) body in
  expect_step "nested RHS search" (R.Search_let (R.Search_let R.Src_async))
    nested
    (let_ x (let_ y addition (t y)) body);
  expect_step "one instruction under nested search"
    (R.Search_let (R.Search_let R.Add))
    (let_ x (let_ y addition (t y)) body)
    (let_ x (let_ y (atom (int 3)) (t y)) body);
  expect_step "inner let only" (R.Search_let R.Let)
    (let_ x (let_ y (atom (int 3)) (t y)) body)
    (let_ x (atom (int 3)) body);
  expect_step "let substitution only" R.Let
    (let_ x (atom (int 3)) body)
    (operation (int 3) Add (int 3));
  no_step "do not search let body" (let_ x (t y) (async (atom (int 1))));
  let open_value = value (pair (a y) nil_atom) in
  expect_step "let accepts an open value" R.Let
    (let_ x (atom open_value) (t x))
    (atom open_value)

let async_and_if () =
  let addition = operation (int 1) Add (int 2) in
  expect_step "async unwraps without evaluating" R.Src_async (async addition)
    addition;
  expect_step "async permits an open body" R.Src_async (async (t x)) (t x);
  expect_step "if true selects without evaluating" R.If_true
    (if_ (bool true) addition (t x))
    addition;
  expect_step "if false selects without evaluating" R.If_false
    (if_ (bool false) (t x) (async addition))
    (async addition)

let matching () =
  List.iter
    (fun (constructor, (pattern, xs), body, expected) ->
      expect_step "constructor match" R.Match_constructor
        (match_ (value constructor)
           [ branch pattern xs body; branch P_wildcard [] (t f) ])
        expected)
    [
      (sexp_int (int 2), (P_int, [ x ]), t x, atom (int 2));
      (sexp_bool (bool true), (P_bool, [ x ]), t x, atom (bool true));
      (sexp_id (id "method"), (P_id, [ x ]), t x, atom (id "method"));
      (nil, (P_nil, []), t x, t x);
      ( pair (a y) nil_atom,
        (P_pair, [ x; y ]),
        pair_term (a x) (a y),
        pair_term (a y) nil_atom );
    ];
  expect_step "select a later constructor branch" R.Match_constructor
    (match_
       (value (sexp_id (id "a")))
       [
         branch P_int [ x ] (t f);
         branch P_id [ x ] (t x);
         branch P_wildcard [] (t f);
       ])
    (atom (id "a"));
  expect_step "wildcard only when no head matches" R.Match_wildcard
    (match_ nil_atom
       [ branch P_int [ x ] (t f); branch P_wildcard [] (async (atom (int 0))) ])
    (async (atom (int 0)));
  (* No hidden field-typing premise in the operational rule. *)
  expect_step "matching inspects the head, not field types" R.Match_constructor
    (match_
       (value (sexp_int (bool true)))
       [ branch P_int [ x ] (t x); branch P_wildcard [] (t f) ])
    (atom (bool true))

let irreducible () =
  let suspended = async (operation (int 1) Add (int 2)) in
  List.iter
    (fun v -> no_step "values do not reduce internally" (atom (value v)))
    [
      integer Z.zero;
      boolean true;
      boolean false;
      unit;
      identifier (Id.of_string "a");
      fun_ [ (x, int_ty) ] int_ty suspended;
      fix f [ (x, int_ty) ] int_ty suspended;
      sexp_int (a x);
      sexp_bool (a x);
      sexp_id (a x);
      nil;
      pair (a x) nil_atom;
    ];
  no_step "free variable is not a value but has no step" (t x);
  List.iter
    (no_step "no rule for these operands")
    [
      operation (bool true) Eq (bool false);
      operation nil_atom Eq nil_atom;
      operation (int 1) Eq (id "one");
      operation (int 1) Add (bool true);
      operation (id "a") Lt (id "b");
      if_ (int 1) suspended suspended;
      if_ (a x) suspended suspended;
    ];
  List.iter
    (fun scrutinee ->
      no_step "wildcard does not match a non-constructor"
        (match_ scrutinee
           [
             branch P_nil [] (atom (int 0)); branch P_wildcard [] (atom (int 1));
           ]))
    [
      int 1;
      bool true;
      value unit;
      a x;
      value (fun_ [ (x, int_ty) ] int_ty (t x));
    ]

(* Only an example runner: the bound prevents a check from hanging. It is not
   part of the calculus and exceeding it would not establish divergence. *)
let run_checked limit input =
  let expected_type = T.type_term Var.Map.empty input in
  let rec run remaining term =
    check "example remains closed" (Var.Set.is_empty (B.fv_term term));
    check "example preserves type"
      (equal_ty expected_type (T.type_term Var.Map.empty term));
    match R.step term with
    | None -> (
        match term with
        | Atom (Value _) -> term
        | _ -> failwith "closed typed example got stuck")
    | Some (_, next) ->
        if remaining = 0 then failwith "example exceeded its step bound";
        run (remaining - 1) next
  in
  run limit input

let finite_executions () =
  let example =
    let_ x
      (let_ y (async (operation (int 1) Add (int 2))) (t y))
      (operation (a x) Add (int 3))
  in
  check "nested let result"
    (B.alpha_equal_term (run_checked 10 example) (atom (int 6)));
  let body =
    let_ y
      (operation (a x) Lt (int 1))
      (if_ (a y)
         (atom (int 0))
         (let_ z (operation (a x) Sub (int 1)) (apply (a f) [ a z ])))
  in
  let countdown = fix f [ (x, int_ty) ] int_ty body in
  check "finite recursive example"
    (B.alpha_equal_term
       (run_checked 40 (async (apply (value countdown) [ int 3 ])))
       (atom (int 0)))

let () =
  List.iter
    (fun (label, run) ->
      run ();
      Printf.printf "Passed reduction: %s\n" label)
    [
      ("primitive rules", primitives);
      ("beta and fix-beta", application);
      ("search and let", search_and_let);
      ("async and conditionals", async_and_if);
      ("constructor and wildcard matching", matching);
      ("terms with no step", irreducible);
      ("finite executions", finite_executions);
    ]

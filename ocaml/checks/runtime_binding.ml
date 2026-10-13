(* Runtime phrase and binding checks only; no typing, reduction or scheduler. *)
open Runtime_calculus
open Runtime_syntax
open Runtime_binding

(* Test notation for constructing the paper's flat patterns. *)
let p_int x = (P_int, [ x ])
let p_bool x = (P_bool, [ x ])
let p_id x = (P_id, [ x ])
let p_nil = (P_nil, [])
let p_pair x y = (P_pair, [ x; y ])
let p_wildcard = (P_wildcard, [])
let branch (head, xs) body = Runtime_syntax.branch head xs body
let x = Var.fresh "x"
let y = Var.fresh "y"
let z = Var.fresh "z"
let u = Var.fresh "u"
let f = Var.fresh "f"
let g = Var.fresh "g"
let p = FName.of_z Z.zero
let q = FName.of_z Z.one
let a = variable
let t x = atom (a x)
let name p = value (future p)
let nil_atom = value nil
let pair_term left right = atom (value (pair left right))
let fn x body = fun_ [ (x, sexp_ty) ] sexp_ty body
let check label condition = if not condition then failwith label

let check_fv label expected actual =
  check label (Var.Set.equal (Var.Set.of_list expected) actual)

let rejects label build =
  match build () with
  | _ -> failwith (label ^ ": accepted invalid syntax")
  | exception Invalid_syntax _ -> ()

let formation () =
  rejects "negative future index" (fun () -> FName.of_z Z.minus_one);
  let huge = Z.of_string "184467440737095516160000000000000000001" in
  check "unbounded future index" (Z.equal huge (FName.to_z (FName.of_z huge)));
  rejects "nullary fun" (fun () -> fun_ [] int_ty (t x));
  rejects "duplicate parameters" (fun () ->
      fun_ [ (x, int_ty); (x, int_ty) ] int_ty (t x));
  rejects "nullary fix" (fun () -> fix f [] int_ty (t x));
  rejects "self equals parameter" (fun () -> fix x [ (x, int_ty) ] int_ty (t x));
  rejects "Pair branch repeated variable" (fun () -> branch (p_pair x x) (t x));
  rejects "Pair branch missing field" (fun () ->
      Runtime_syntax.branch P_pair [ x ] (t x));
  rejects "Nil branch with binder" (fun () ->
      Runtime_syntax.branch P_nil [ x ] (t x));
  rejects "nullary application" (fun () -> apply (name p) []);
  let default = branch p_wildcard (atom nil_atom) in
  let case = branch p_nil (atom (name p)) in
  rejects "empty match" (fun () -> match_ (a x) []);
  rejects "wildcard only" (fun () -> match_ (a x) [ default ]);
  rejects "missing wildcard" (fun () -> match_ (a x) [ case ]);
  rejects "early wildcard" (fun () -> match_ (a x) [ default; case ]);
  rejects "repeated wildcard" (fun () ->
      match_ (a x) [ case; default; default ]);
  rejects "repeated constructor head" (fun () ->
      match_ (a x) [ branch (p_int x) (t x); branch (p_int y) (t y); default ]);
  ignore (apply (value (fn x (t x))) [ name p; name q ]);
  (* Formation does not enforce typing, arity agreement or closedness. *)
  check "open, ill-typed constructor is formed"
    (formed_value FName.Set.empty (sexp_bool (a x)))

(* Put the only future occurrence in each recursive grammar position. The
   formation check must visit bodies and branches, not just active redexes. *)
let placements b =
  let body = atom b and plain = atom nil_atom in
  let term w = atom (value w) in
  [
    body;
    term (fn x body);
    term (fix f [ (x, sexp_ty) ] sexp_ty body);
    term (sexp_int b);
    term (sexp_bool b);
    term (sexp_id b);
    pair_term b nil_atom;
    pair_term nil_atom b;
    apply b [ nil_atom ];
    apply (a f) [ nil_atom; b ];
    operation b Add nil_atom;
    operation nil_atom Eq b;
    if_ b plain plain;
    if_ nil_atom body plain;
    if_ nil_atom plain body;
    let_ x body plain;
    let_ x plain body;
    match_ b [ branch p_nil plain; branch p_wildcard plain ];
    match_ nil_atom [ branch p_nil body; branch p_wildcard plain ];
    match_ nil_atom [ branch p_nil plain; branch p_wildcard body ];
    match_ nil_atom [ branch (p_int x) body; branch p_wildcard plain ];
    match_ nil_atom [ branch (p_bool x) body; branch p_wildcard plain ];
    match_ nil_atom [ branch (p_id x) body; branch p_wildcard plain ];
    match_ nil_atom [ branch (p_pair x y) body; branch p_wildcard plain ];
    async body;
  ]

let scope_and_exchange () =
  List.iter
    (fun term ->
      check "future occurrence needs an active name"
        (not (formed_term FName.Set.empty term));
      check "active future is formed" (formed_term (FName.Set.singleton p) term);
      check "additional active names are allowed"
        (formed_term (FName.Set.of_list [ p; q ]) term);
      let renamed = exchange_future_term p q term in
      check "exchange transports active names"
        (formed_term (FName.Set.singleton q) renamed
        && not (formed_term (FName.Set.singleton p) renamed));
      check "future exchange is an involution"
        (alpha_equal_term term (exchange_future_term p q renamed));
      check "future exchange fixes source variables"
        (Var.Set.equal (fv_term term) (fv_term renamed));
      check "source-variable exchange fixes future names"
        (formed_term (FName.Set.singleton p) (exchange_term x y term)))
    (placements (name p));
  let shared = pair_term (name p) (name p) in
  check "shared futures are legal" (formed_term (FName.Set.singleton p) shared);
  check "future exchange swaps both names"
    (alpha_equal_term
       (exchange_future_term p q (pair_term (name p) (name q)))
       (pair_term (name q) (name p)));
  check_fv "future is not a source variable" [] (fv_value (future p));
  check "variable substitution fixes future names"
    (alpha_equal_value (future p) (subst_value (single x (name q)) (future p)))

let alpha_and_binders () =
  check "future names are exact in phrase alpha comparison"
    (not (alpha_equal_value (future p) (future q)));
  check "bound source variables may differ"
    (alpha_equal_value
       (fn x (pair_term (a x) (name p)))
       (fn y (pair_term (a y) (name p))));
  check "binder renaming cannot change futures"
    (not
       (alpha_equal_value
          (fn x (pair_term (a x) (name p)))
          (fn y (pair_term (a y) (name q)))));
  check_fv "fix binds self and parameters" [ y ]
    (fv_value
       (fix f [ (x, sexp_ty) ] sexp_ty (apply (a f) [ a x; a y; name p ])));
  check_fv "let binds only its body" [ x ]
    (fv_term (let_ x (t x) (pair_term (a x) (name p))));
  check_fv "pattern binds only its branch body" [ x; z ]
    (fv_term
       (match_ (a x)
          [
            branch (p_pair x y) (pair_term (a y) (name p));
            branch p_wildcard (t z);
          ]));
  check "nested shadowing"
    (alpha_equal_value
       (fn x (atom (value (fn x (pair_term (a x) (name p))))))
       (fn y (atom (value (fn z (pair_term (a z) (name p)))))));
  let literal = identifier (Id.of_string "x") in
  check "identifier is neither variable nor future"
    (alpha_equal_value literal (subst_value (single x (name p)) literal)
    && alpha_equal_value literal (exchange_future_value p q literal)
    && alpha_equal_value literal (exchange_value x y literal))

let substitution () =
  let replacement = value (pair (a y) (name p)) in
  let result = subst_value (single x replacement) (fn y (t x)) in
  check "freshen function binder, preserve free variable and future"
    (alpha_equal_value result (fn z (atom replacement)));
  check_fv "capture avoided" [ y ] (fv_value result);
  check "replacement active names preserved"
    (formed_value (FName.Set.singleton p) result);
  let recursive = fix f [ (y, sexp_ty) ] sexp_ty (pair_term (a x) (a f)) in
  check "freshen self binder"
    (alpha_equal_value
       (subst_value (single x (value (pair (a f) (name p)))) recursive)
       (fix g
          [ (y, sexp_ty) ]
          sexp_ty
          (pair_term (value (pair (a f) (name p))) (a g))));
  check "fix self is not substituted"
    (alpha_equal_value recursive (subst_value (single f (name p)) recursive));
  check "let rhs is outside binding scope"
    (alpha_equal_term
       (subst_term (single x (name p)) (let_ x (t x) (t x)))
       (let_ x (atom (name p)) (t x)));
  check "freshen Pair pattern and its body together"
    (alpha_equal_branch
       (subst_branch
          (single z (value (pair (a x) (name p))))
          (branch (p_pair x y) (pair_term (a z) (a x))))
       (branch (p_pair u y) (pair_term (value (pair (a x) (name p))) (a u))));
  let simultaneous_subst = simultaneous [ (x, a y); (y, name p) ] in
  check "simultaneous replacements are not recursively substituted"
    (alpha_equal_term
       (subst_term simultaneous_subst (pair_term (a x) (a y)))
       (pair_term (a y) (name p)));
  (match simultaneous [ (x, name p); (x, name q) ] with
  | _ -> failwith "duplicate substitution domain accepted"
  | exception Invalid_argument _ -> ());
  List.iter2
    (fun before expected ->
      let after = subst_term (single z (name p)) before in
      check "substitution visits every grammar position"
        (alpha_equal_term after expected);
      check "empty substitution is identity"
        (alpha_equal_term before (subst_term empty before)))
    (placements (a z))
    (placements (name p))

let source_conversion () =
  let open Source_calculus in
  let open Syntax in
  let rx, ry, rz, rf = (x, y, z, f) in
  let x = Var.fresh "x"
  and y = Var.fresh "y"
  and z = Var.fresh "z"
  and f = Var.fresh "f" in
  let free =
    List.fold_left
      (fun env (x, y) -> Runtime_input.add x y env)
      Runtime_input.empty
      [ (x, rx); (y, ry); (z, rz); (f, rf) ]
  in
  let of_source_term = Runtime_input.term ~free in
  let of_source_atom = Runtime_input.atom ~free in
  let ta x = atom (variable x) in
  let native_values =
    [
      integer (Z.of_int 7);
      boolean true;
      unit;
      identifier (Id.of_string "x");
      nil;
    ]
  in
  let cases =
    [
      (P_int, [ x ]);
      (P_bool, [ x ]);
      (P_id, [ x ]);
      (P_nil, []);
      (P_pair, [ x; y ]);
      (P_wildcard, []);
    ]
  in
  let terms =
    List.map (fun v -> atom (value v)) native_values
    @ [
        atom (value (fun_ [ (x, sexp_ty) ] sexp_ty (ta y)));
        atom
          (value
             (fix f
                [ (x, sexp_ty) ]
                sexp_ty
                (apply (variable f) [ variable x ])));
        atom (value (sexp_int (variable x)));
        atom (value (sexp_bool (variable x)));
        atom (value (sexp_id (variable x)));
        atom (value (pair (variable x) (variable y)));
        if_ (variable z) (ta x) (ta y);
        let_ x (async (ta y)) (ta x);
        match_ (variable z)
          (List.map (fun (pat, xs) -> branch pat xs (ta x)) cases);
      ]
    @ List.map
        (fun op -> operation (variable x) op (variable y))
        [ Add; Sub; Mul; Eq; Lt ]
  in
  let replacement = value (pair (variable x) (value nil)) in
  List.iter
    (fun source ->
      let runtime = of_source_term source in
      check "source conversion is formed at empty active set"
        (formed_term FName.Set.empty runtime);
      check "source conversion preserves FV"
        (Runtime_syntax.Var.Set.equal
           (Var.Set.fold
              (fun source_variable vars ->
                Runtime_syntax.Var.Set.add
                  (snd
                     (List.find
                        (fun (s, _) -> Var.equal s source_variable)
                        [ (x, rx); (y, ry); (z, rz); (f, rf) ]))
                  vars)
              (Binding.fv_term source) Runtime_syntax.Var.Set.empty)
           (fv_term runtime));
      check "source conversion commutes with variable exchange"
        (alpha_equal_term
           (exchange_term rx ry runtime)
           (of_source_term (Binding.exchange_term x y source)));
      check "source conversion commutes with capture-avoiding substitution"
        (alpha_equal_term
           (subst_term (single ry (of_source_atom replacement)) runtime)
           (of_source_term
              (Binding.subst_term (Binding.single y replacement) source))))
    terms;
  match
    of_source_term
      (async (operation (value (integer Z.one)) Add (value (integer Z.one))))
  with
  | Runtime_syntax.Async (Runtime_syntax.Operation (_, Add, _)) -> ()
  | _ -> failwith "source conversion changed async or reduced its body"

let instantiate_binders () =
  let sum =
    fun_ [ (x, int_ty); (y, int_ty) ] int_ty (operation (a x) Add (a y))
  in
  (match sum with
  | Fun (_, _, body) ->
      check "function binder simultaneous argument order"
        (alpha_equal_term
           (Bindlib.msubst body [| name p; name q |])
           (operation (name p) Add (name q)))
  | _ -> failwith "expected function");
  let recursive = fix f [ (x, sexp_ty) ] sexp_ty (apply (a f) [ a x ]) in
  (match recursive with
  | Fix (_, _, body) ->
      check "fix binds self before arguments"
        (alpha_equal_term
           (Bindlib.msubst body [| value recursive; name p |])
           (apply (value recursive) [ name p ]))
  | _ -> failwith "expected fix");
  (match branch (p_pair x y) (pair_term (a x) (a y)) with
  | Branch (_, body) ->
      check "Pair branch substitutes fields left to right"
        (alpha_equal_term
           (Bindlib.msubst body [| name p; name q |])
           (pair_term (name p) (name q))));
  List.iter
    (fun pat ->
      match branch pat (t x) with
      | Branch (_, body) ->
          check "zero-field branch leaves its body open"
            (alpha_equal_term (Bindlib.msubst body [||]) (t x)))
    [ p_nil; p_wildcard ];
  check "box traversal exposes variables in an existing binder"
    (Bindlib.occur x (box_value (fn y (t x))));
  check "future is not a Bindlib variable"
    (Bindlib.is_closed (box_atom (name p))
    && not (formed_atom FName.Set.empty (name p)))

let input_and_display () =
  let read ?(free = []) text =
    match Source_frontend.Frontend.toplevel ~free (Lexing.from_string text) with
    | Ok command -> command.Zoo.data
    | Error (_, error) -> failwith error
  in
  let display term = Format.asprintf "%a" Runtime_print.term term in
  List.iter
    (fun text ->
      let source = read text in
      let runtime = Runtime_input.term source in
      check "text conversion is closed and future-free"
        (Var.Set.is_empty (fv_term runtime)
        && formed_term FName.Set.empty runtime);
      let shown = display runtime in
      check
        ("runtime display round trip: " ^ shown)
        (alpha_equal_term runtime (Runtime_input.term (read shown))))
    [
      "let x = async (1 + 2) in x + 3";
      "fun (x : int) : (int) -> int is fun (x : int) : int is x";
      "fun (x : int) : int is let x = x in x";
      "fix f(x : int) : int is let y = x - 1 in f(y)";
      "fun (f : (int) -> int, x : int) : int is f(x)";
      "match Pair(Int(1), Nil) { Pair(x,y) => x | _ => Nil }";
      "fun (x : sexp) : sexp is match x { Pair(x,y) => y | _ => x }";
      "match Nil { Int(x) => () | Bool(x) => () | Id(x) => () | Nil => () | \
       Pair(x,y) => () | _ => () }";
      "if true then Id(\"ClassName\") else Bool(false)";
    ];
  (* Unlike alpha comparison alone, this checks which binder each occurrence uses. *)
  let bound =
    Runtime_input.term (read "fun (x : int) : int is let x = x in x")
  in
  (match bound with
  | Atom (Value (Fun (_, _, body))) -> (
      match Bindlib.msubst body [| name p |] with
      | Let (rhs, body) ->
          check "text let RHS refers to outer binding"
            (alpha_equal_term rhs (atom (name p)));
          check "text let body refers to inner binding"
            (alpha_equal_term (Bindlib.subst body (name q)) (atom (name q)))
      | _ -> failwith "expected let")
  | _ -> failwith "expected function");
  (match Runtime_input.term (read "x") with
  | _ -> failwith "unbound input silently accepted"
  | exception Runtime_input.Unbound_variable _ -> ());
  let module S = Source_calculus.Syntax in
  let sx = S.Var.fresh "x" and sy = S.Var.fresh "y" in
  let free = Runtime_input.add sx x Runtime_input.empty in
  (match Runtime_input.add sy x free with
  | _ -> failwith "free-variable conversion merged identities"
  | exception Invalid_argument _ -> ());
  let x1 = Var.fresh "x" and x2 = Var.fresh "x" in
  check "identical display hints do not identify free variables"
    (not (alpha_equal_atom (a x1) (a x2)));
  check "different free identities print differently"
    (display (pair_term (a x1) (a x2)) <> "Pair(x, x)");
  let captured = subst_value (single x (a y)) (fn y (t x)) in
  let shown = Format.asprintf "%a" Runtime_print.value captured in
  let free = Runtime_input.add sy y Runtime_input.empty in
  check "printed substitution keeps y free"
    (alpha_equal_term
       (atom (value captured))
       (Runtime_input.term ~free (read ~free:[ ("y", sy) ] shown)));
  check "future display is not a variable or identifier literal"
    (display
       (pair_term (name p) (value (identifier (Id.of_string "future(0)"))))
    = "Pair(future(0), \"future(0)\")");
  check "non-lexical variable hints do not print as future names"
    (display (t (Var.fresh "future(0)")) = "var(\"future(0)\")");
  check "printing does not change future formation"
    (formed_term (FName.Set.singleton p) (pair_term (name p) (a y)))

let () =
  List.iter
    (fun (label, run) ->
      run ();
      Printf.printf "Passed: %s\n" label)
    [
      ("runtime formation", formation);
      ("future scope and exchange", scope_and_exchange);
      ("runtime alpha and binders", alpha_and_binders);
      ("runtime substitution", substitution);
      ("source conversion", source_conversion);
      ("binder instantiation", instantiate_binders);
      ("text conversion and binding-safe display", input_and_display);
    ]

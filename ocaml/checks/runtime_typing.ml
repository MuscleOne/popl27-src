open Runtime_calculus
open Runtime_syntax
module State = Runtime_state
module Typing = Runtime_typing

let check label condition = if not condition then failwith label
let empty = FName.Map.empty
let p = FName.of_z Z.zero
let q = FName.of_z Z.one
let r = FName.of_z (Z.of_int 2)
let x = Var.fresh "x"
let y = Var.fresh "y"
let f = Var.fresh "f"
let name p = value (future p)
let int n = value (integer (Z.of_int n))
let nil_atom = value nil
let infer signature term = Typing.type_term signature Var.Map.empty term

let has_type signature term expected =
  check "runtime type" (equal_ty (infer signature term) expected)

let rejects label accepts run =
  match run () with
  | _ -> failwith (label ^ ": accepted invalid typing")
  | exception Typing.Type_error error -> check label (accepts error)

let mismatch rule = function
  | Typing.Type_mismatch { rule = actual; _ } -> actual = rule
  | _ -> false

let future_typing () =
  let signature =
    FName.Map.(
      empty |> add p int_ty |> add q sexp_ty |> add r (arrow [ int_ty ] bool_ty))
  in
  (* There is deliberately no mapping: T-Future needs only a declaration. *)
  has_type signature (atom (name p)) int_ty;
  has_type signature (atom (value (pair (name q) nil_atom))) sexp_ty;
  rejects "Pair requires sexp, even for a future"
    (mismatch "T-Constructor-Pair") (fun () ->
      infer signature (atom (value (pair (name p) nil_atom))));
  rejects "undeclared future"
    (function Typing.Unbound_future name -> FName.equal name p | _ -> false)
    (fun () -> infer empty (atom (name p)));
  has_type signature (apply (name r) [ name p ]) bool_ty;
  rejects "future function checks argument types" (mismatch "T-App") (fun () ->
      infer signature (apply (name r) [ name q ]));
  rejects "future function checks arity"
    (function Typing.Arity_mismatch _ -> true | _ -> false)
    (fun () -> infer signature (apply (name r) [ name p; name p ]));
  has_type signature (let_ x (async (atom (name p))) (atom (variable x))) int_ty;
  has_type signature
    (atom (value (fun_ [ (x, int_ty) ] int_ty (atom (name p)))))
    (arrow [ int_ty ] int_ty);
  has_type signature
    (atom
       (value (fix f [ (x, int_ty) ] int_ty (apply (variable f) [ name p ]))))
    (arrow [ int_ty ] int_ty);
  rejects "annotation under binder" (mismatch "T-Fun") (fun () ->
      infer signature
        (atom (value (fun_ [ (x, int_ty) ] bool_ty (atom (name p))))));
  List.iter
    (fun op -> has_type signature (operation (name p) op (int 1)) int_ty)
    [ Add; Sub; Mul ];
  List.iter
    (fun op -> has_type signature (operation (name p) op (int 1)) bool_ty)
    [ Eq; Lt ];
  rejects "sexp equality remains unsupported"
    (function Typing.Equality_type Ty_sexp -> true | _ -> false)
    (fun () -> infer signature (operation (name q) Eq (name q)));
  let cases =
    [
      branch P_pair [ x; y ] (atom (variable x));
      branch P_wildcard [] (atom (name q));
    ]
  in
  has_type signature (match_ (name q) cases) sexp_ty;
  rejects "wildcard also checked" (mismatch "T-Match") (fun () ->
      infer signature
        (match_ (name q)
           [
             branch P_nil [] (atom nil_atom);
             branch P_wildcard [] (atom (name p));
           ]));
  rejects "let variable not in RHS scope"
    (function Typing.Unbound_variable z -> Var.equal z x | _ -> false)
    (fun () -> infer signature (let_ x (atom (variable x)) (atom (name p))))

let state_typing () =
  let signature = FName.Map.(empty |> add p int_ty |> add q int_ty) in
  let aliases =
    FName.Map.(empty |> add p (atom (name q)) |> add q (atom (name p)))
  in
  let cyclic = State.make signature (atom (name p)) aliases in
  check "State-Ok permits mutual aliases"
    (equal_ty (Typing.check_state cyclic) int_ty && State.final cyclic);
  let self =
    State.make
      (FName.Map.singleton p int_ty)
      (atom (name p))
      (FName.Map.singleton p (atom (name p)))
  in
  check "State-Ok permits self alias"
    (equal_ty (Typing.check_state self) int_ty);
  let renamed = State.exchange_futures p r cyclic in
  check "consistent future renaming preserves typing"
    (equal_ty (Typing.check_state renamed) int_ty);
  let pending =
    State.make signature
      (atom (name p))
      (FName.Map.add p (async (atom (int 1))) aliases)
  in
  check "State-Ok does not demand finality"
    (equal_ty (Typing.check_state pending) int_ty && not (State.final pending));
  let rejects_state label accepts state =
    match Typing.check_state state with
    | _ -> failwith (label ^ ": accepted invalid State-Ok")
    | exception Typing.State_error error -> check label (accepts error)
  in
  rejects_state "missing mapping entries"
    (function Typing.Domain_mismatch -> true | _ -> false)
    (State.make signature (atom (name p)) empty);
  rejects_state "free variable in focus"
    (function
      | Typing.Focus_type_error (Typing.Unbound_variable z) -> Var.equal z x
      | _ -> false)
    (State.make empty (atom (variable x)) empty);
  rejects_state "free variable in mapped term"
    (function
      | Typing.Entry_type_error (n, Typing.Unbound_variable z) ->
          FName.equal n p && Var.equal z x
      | _ -> false)
    (State.make signature
       (atom (int 0))
       (FName.Map.add p (atom (variable x)) aliases));
  rejects_state "entry disagrees with declared type"
    (function
      | Typing.Entry_type_error (n, e) ->
          FName.equal n p && mismatch "State-Ok" e
      | _ -> false)
    (State.make signature
       (atom (int 0))
       (FName.Map.add p (atom (value (boolean true))) aliases));
  rejects_state "formed ill-typed focus"
    (function Typing.Focus_type_error e -> mismatch "T-Arith" e | _ -> false)
    (State.make empty (operation (value (boolean true)) Add (int 1)) empty)

let source_programs () =
  (* Empty-signature agreement on real source text, not runtime reduction. *)
  List.iter
    (fun text ->
      let source =
        match Source_frontend.Frontend.toplevel (Lexing.from_string text) with
        | Ok command -> command.Zoo.data
        | Error (_, message) -> failwith (text ^ ": " ^ message)
      in
      let expected =
        Source_calculus.Typing.type_term Source_calculus.Syntax.Var.Map.empty
          source
      in
      let initial = State.make empty (Runtime_input.term source) empty in
      check text (equal_ty (Typing.check_state initial) expected))
    [
      "let x = async (1 + 2) in x + x";
      "let x = 1 in let x = x + 2 in x";
      "(fun (x : int) : bool is x < 2)(1)";
      "fix f(x : int) : int is let done_ = x = 0 in if done_ then 0 else let y \
       = x - 1 in f(y)";
      "Pair(Int(1), Bool(true))";
      "match Id(\"A\") { Id(x) => x = \"A\" | _ => false }";
    ]

let () =
  future_typing ();
  state_typing ();
  source_programs ();
  print_endline "Runtime typing and State-Ok checks passed"

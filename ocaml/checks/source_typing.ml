(* Checks of section 6 rule premises, not an OO checker or a reduction test. *)
open Source_calculus.Syntax
open Source_calculus.Typing
module Binding = Source_calculus.Binding

let x = Var.fresh "x"
let y = Var.fresh "y"
let f = Var.fresh "f"
let a = variable
let t x = atom (a x)
let int n = value (integer (Z.of_int n))
let bool b = value (boolean b)
let id s = value (identifier (Id.of_string s))
let nil_atom = value nil
let closed = Var.Map.empty
let check label condition = if not condition then failwith label

let has_type label environment term expected =
  check label (equal_ty (type_term environment term) expected)

let rejects label expected_error run =
  match run () with
  | _ -> failwith (label ^ ": accepted an ill-typed term")
  | exception Type_error error ->
      check (label ^ ": unexpected error") (expected_error error)

let mismatch rule = function Type_mismatch e -> e.rule = rule | _ -> false

let unbound name = function
  | Unbound_variable x -> Var.equal name x
  | _ -> false

let literals_and_variables () =
  List.iter
    (fun (literal, ty) -> has_type "literal" closed (atom literal) ty)
    [
      (int 1, int_ty);
      (bool true, bool_ty);
      (bool false, bool_ty);
      (value unit, unit_ty);
      (id "x", id_ty);
    ];
  has_type "variable lookup" (Var.Map.singleton x sexp_ty) (t x) sexp_ty;
  rejects "unbound variable" (unbound x) (fun () -> type_term closed (t x))

let functions () =
  let choose =
    fun_ [ (x, bool_ty); (y, int_ty) ] int_ty (if_ (a x) (t y) (atom (int 0)))
  in
  has_type "annotated function" closed
    (atom (value choose))
    (arrow [ bool_ty; int_ty ] int_ty);
  has_type "argument order" closed
    (apply (value choose) [ bool true; int 7 ])
    int_ty;
  rejects "reversed arguments" (mismatch "T-App") (fun () ->
      type_term closed (apply (value choose) [ int 7; bool true ]));
  rejects "arity"
    (function
      | Arity_mismatch { expected = 2; actual = 1 } -> true | _ -> false)
    (fun () -> type_term closed (apply (value choose) [ bool true ]));
  rejects "non-function"
    (function Not_function Ty_int -> true | _ -> false)
    (fun () -> type_term closed (apply (int 1) [ int 2 ]));
  rejects "return annotation" (mismatch "T-Fun") (fun () ->
      type_value closed (fun_ [ (x, int_ty) ] bool_ty (t x)));
  (* Self recursion is type checked, not evaluated or required to terminate. *)
  let recursive = fix f [ (x, int_ty) ] int_ty (apply (a f) [ a x ]) in
  check "fix self type"
    (equal_ty
       (type_value (Var.Map.singleton f bool_ty) recursive)
       (arrow [ int_ty ] int_ty));
  rejects "fix return annotation" (mismatch "T-Fix") (fun () ->
      type_value closed (fix f [ (x, int_ty) ] bool_ty (t x)));
  rejects "fun has no implicit self binder" (unbound f) (fun () ->
      type_value closed (fun_ [ (x, int_ty) ] int_ty (apply (a f) [ a x ])))

let constructors () =
  List.iter
    (fun v -> check "constructor" (equal_ty (type_value closed v) sexp_ty))
    [
      sexp_int (int 1);
      sexp_bool (bool true);
      sexp_id (id "class");
      nil;
      pair (value (sexp_int (int 1))) nil_atom;
    ];
  check "open field"
    (equal_ty
       (type_value (Var.Map.singleton x sexp_ty) (pair (a x) nil_atom))
       sexp_ty);
  rejects "native int is not sexp" (mismatch "T-Constructor-Pair") (fun () ->
      type_value closed (pair (int 1) nil_atom));
  List.iter
    (fun (rule, malformed) ->
      rejects rule (mismatch rule) (fun () -> type_value closed malformed))
    [
      ("T-Constructor-Int", sexp_int (bool true));
      ("T-Constructor-Bool", sexp_bool (int 1));
      ("T-Constructor-Id", sexp_id (int 1));
      ("T-Constructor-Pair", pair nil_atom (bool false));
    ]

let operators () =
  List.iter
    (fun op ->
      has_type "arithmetic" closed (operation (int 1) op (int 2)) int_ty)
    [ Add; Sub; Mul ];
  has_type "integer ordering" closed (operation (int 1) Lt (int 2)) bool_ty;
  has_type "integer equality" closed (operation (int 1) Eq (int 2)) bool_ty;
  has_type "identifier equality" closed (operation (id "a") Eq (id "b")) bool_ty;
  List.iter
    (fun operand ->
      rejects "equality domain"
        (function Equality_type _ -> true | _ -> false)
        (fun () -> type_term closed (operation operand Eq operand)))
    [
      bool true; value unit; nil_atom; value (fun_ [ (x, int_ty) ] int_ty (t x));
    ];
  rejects "mixed equality" (mismatch "T-Eq") (fun () ->
      type_term closed (operation (int 1) Eq (id "one")));
  rejects "arithmetic operand" (mismatch "T-Arith") (fun () ->
      type_term closed (operation (int 1) Add (bool true)));
  rejects "ordering operand" (mismatch "T-Lt") (fun () ->
      type_term closed (operation (id "a") Lt (id "b")))

let scope_and_branches () =
  let environment = Var.Map.singleton x bool_ty in
  has_type "let rhs uses outer environment" environment
    (let_ x (if_ (a x) (atom (int 1)) (atom (int 2))) (t x))
    int_ty;
  check "environment is persistent"
    (equal_ty (Var.Map.find x environment) bool_ty);
  rejects "let cannot bind its rhs" (unbound x) (fun () ->
      type_term closed (let_ x (t x) (t x)));
  check "fun shadows outer parameter"
    (equal_ty
       (type_value environment (fun_ [ (x, int_ty) ] int_ty (t x)))
       (arrow [ int_ty ] int_ty));
  List.iter
    (fun ((pattern, xs), body, ty) ->
      check "branch field type"
        (equal_ty (type_branch environment (branch pattern xs body)) ty))
    [
      ((P_int, [ x ]), t x, int_ty);
      ((P_bool, [ x ]), t x, bool_ty);
      ((P_id, [ x ]), t x, id_ty);
      ((P_nil, []), t x, bool_ty);
      ((P_pair, [ x; y ]), atom (value (pair (a x) (a y))), sexp_ty);
      ((P_wildcard, []), t x, bool_ty);
    ];
  let matching =
    match_ nil_atom
      [ branch P_int [ x ] (t x); branch P_wildcard [] (atom (int 0)) ]
  in
  has_type "common branch result" closed matching int_ty;
  has_type "async preserves type" closed (async matching) int_ty;
  rejects "scrutinee must be sexp" (mismatch "T-Match") (fun () ->
      type_term closed
        (match_ (int 1)
           [
             branch P_nil [] (atom (int 0)); branch P_wildcard [] (atom (int 0));
           ]));
  rejects "wildcard result type" (mismatch "T-Match") (fun () ->
      type_term closed
        (match_ nil_atom
           [
             branch P_nil [] (atom (int 0));
             branch P_wildcard [] (atom (bool true));
           ]));
  rejects "branch scope does not leak" (unbound x) (fun () ->
      type_term closed
        (match_ nil_atom
           [ branch P_int [ x ] (t x); branch P_wildcard [] (t x) ]));
  rejects "check unselected branches too" (mismatch "T-Arith") (fun () ->
      type_term closed
        (match_ nil_atom
           [
             branch P_bool [ x ] (operation (a x) Add (int 1));
             branch P_wildcard [] (atom (int 0));
           ]));
  rejects "conditional guard" (mismatch "T-If") (fun () ->
      type_term closed (if_ (int 1) (atom (int 1)) (atom (int 2))));
  rejects "conditional branch types" (mismatch "T-If") (fun () ->
      type_term closed (if_ (bool true) (atom (int 1)) (atom (bool false))));
  rejects "async checks its body" (unbound x) (fun () ->
      type_term closed (async (t x)))

let substitution_example () =
  (* One concrete instance of S-Substitution, not a proof of that theorem. *)
  let original = atom (value (fun_ [ (y, int_ty) ] bool_ty (t x))) in
  let ty = arrow [ int_ty ] bool_ty in
  let environment = Var.Map.singleton y bool_ty in
  has_type "before substitution" (Var.Map.add x bool_ty environment) original ty;
  has_type "replacement atom" environment (t y) bool_ty;
  has_type "after capture-avoiding substitution" environment
    (Binding.subst_term (Binding.single x (a y)) original)
    ty

let () =
  List.iter
    (fun (label, run) ->
      run ();
      Printf.printf "Passed typing: %s\n" label)
    [
      ("literals and variables", literals_and_variables);
      ("functions and application", functions);
      ("sexp constructors", constructors);
      ("operator domains", operators);
      ("scope and branches", scope_and_branches);
      ("substitution example", substitution_example);
    ]

open Source_calculus
open Syntax

let expect print input expected =
  let actual = Format.asprintf "%a" print input in
  if actual <> expected then
    failwith (Printf.sprintf "Expected %S, printed %S" expected actual)

let x = Var.fresh "x"
let y = Var.fresh "y"
let f = Var.fresh "f"
let int n = value (integer (Z.of_int n))
let t = atom (variable x)

let () =
  List.iter
    (fun (ty, text) -> expect Print.ty ty text)
    [
      (int_ty, "int");
      (bool_ty, "bool");
      (unit_ty, "unit");
      (id_ty, "id");
      (sexp_ty, "sexp");
      ( arrow [ int_ty; arrow [ bool_ty ] sexp_ty ] unit_ty,
        "(int, (bool) -> sexp) -> unit" );
    ];
  expect Print.atom (variable x) "x";
  expect Print.atom (variable (Var.fresh "Nil")) "Nil1";
  expect Print.atom (variable (Var.fresh "x\ny")) "var(\"x\\ny\")";
  expect Print.value (identifier (Id.of_string "x")) "\"x\"";
  expect Print.value (identifier (Id.of_string "a\"b\n")) "\"a\\\"b\\n\"";
  expect Print.value
    (integer (Z.of_string "18446744073709551616"))
    "18446744073709551616";
  expect Print.value unit "()";
  expect Print.value (boolean false) "false";
  expect Print.value (sexp_bool (value (boolean true))) "Bool(true)";
  expect Print.value
    (sexp_id (value (identifier (Id.of_string "C"))))
    "Id(\"C\")";
  expect Print.value
    (pair (value (sexp_int (int 1))) (value nil))
    "Pair(Int(1), Nil)";
  expect Print.term
    (apply (value (fun_ [ (x, int_ty) ] int_ty t)) [ int 1 ])
    "(fun (x : int) : int is x)(1)";
  expect Print.value
    (fix f [ (x, int_ty) ] int_ty (apply (variable f) [ variable x ]))
    "(fix f(x : int) : int is f(x))";
  expect Print.term
    (let_ x (let_ y (atom (int 1)) (atom (variable y))) t)
    "let x = (let y = (1) in y) in x";
  expect Print.term (async (let_ x (atom (int 1)) t)) "async (let x = (1) in x)";
  expect Print.term
    (if_ (value (boolean true)) t (atom (int 0)))
    "if true then (x) else (0)";
  List.iter
    (fun (op, text) -> expect Print.term (operation (int 1) op (int 2)) text)
    [
      (Add, "1 + 2");
      (Sub, "1 - 2");
      (Mul, "1 * 2");
      (Eq, "1 = 2");
      (Lt, "1 < 2");
    ];
  List.iter
    (fun ((pat, xs), text) ->
      expect Print.branch (branch pat xs (atom (int 0))) (text ^ " => 0"))
    [
      ((P_int, [ x ]), "Int(x)");
      ((P_bool, [ x ]), "Bool(x)");
      ((P_id, [ x ]), "Id(x)");
      ((P_nil, []), "Nil");
      ((P_pair, [ x; y ]), "Pair(x, y)");
      ((P_wildcard, []), "_");
    ];
  expect Print.term
    (match_ (variable x)
       [ branch P_nil [] (atom (int 0)); branch P_wildcard [] (atom (int 1)) ])
    "match x { Nil => 0 | _ => 1 }";
  List.iter
    (fun (error, text) -> expect Print.error error text)
    Typing.
      [
        (Unbound_variable x, "Unbound variable x");
        ( Type_mismatch { rule = "T-If"; expected = bool_ty; actual = int_ty },
          "T-If: expected bool, found int" );
        (Not_function sexp_ty, "Application expects a function, found sexp");
        ( Arity_mismatch { expected = 2; actual = 1 },
          "Application expects 2 argument(s), found 1" );
        ( Equality_type bool_ty,
          "Equality expects int or id operands, found bool" );
      ];
  expect Print.rule
    Reduction.(Search_let (Search_let Src_async))
    "Search-Let(Search-Let(Src-Async))";
  print_endline "Passed source syntax and diagnostic printing"

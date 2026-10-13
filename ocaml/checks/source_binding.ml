(* A small set of executable examples for source-calculus.md sections 1--5.
   No evaluation rules or typechecker are used here. *)
open Source_calculus.Syntax
open Source_calculus.Binding

let x = Var.fresh "x"
let y = Var.fresh "y"
let z = Var.fresh "z"
let u = Var.fresh "u"
let f = Var.fresh "f"
let a x = variable x
let t x = atom (a x)
let int n = value (integer (Z.of_int n))
let nil_atom = value nil
let pair_term left right = atom (value (pair left right))
let fn x body = fun_ [ (x, int_ty) ] int_ty body
let check label condition = if not condition then failwith label

let check_fv label expected actual =
  check label (Var.Set.equal (Var.Set.of_list expected) actual)

let rejects label build =
  match build () with
  | _ -> failwith (label ^ ": accepted invalid syntax")
  | exception Invalid_syntax _ -> ()

let data () =
  let huge = Z.of_string "184467440737095516160000000000000000001" in
  (match integer huge with
  | Integer n -> check "unbounded integer" (Z.equal n huge)
  | _ -> failwith "integer representation");
  let literal = value (identifier (Id.of_string "x")) in
  check_fv "identifier is not a variable" [] (fv_atom literal);
  check "substitution fixes identifiers"
    (alpha_equal_atom literal (subst_atom (single x (int 1)) literal));
  check "native int differs from injected int"
    (not (alpha_equal_atom (int 1) (value (sexp_int (int 1)))));
  (* Formation is not typing: an open constructor field is valid syntax. *)
  check_fv "constructor fields may be open atoms" [ x ]
    (fv_value (sexp_bool (a x)))

let formation () =
  rejects "nullary arrow" (fun () -> arrow [] int_ty);
  rejects "nullary fun" (fun () -> fun_ [] int_ty (t x));
  rejects "repeated parameter" (fun () ->
      fun_ [ (x, int_ty); (x, int_ty) ] int_ty (t x));
  rejects "nullary fix" (fun () -> fix f [] int_ty (t x));
  rejects "self equals parameter" (fun () -> fix x [ (x, int_ty) ] int_ty (t x));
  rejects "nullary application" (fun () -> apply (a f) []);
  rejects "repeated Pair binder" (fun () -> branch P_pair [ x; x ] (t x));
  let wildcard = branch P_wildcard [] (t z) in
  let nil_case = branch P_nil [] (t z) in
  rejects "empty match" (fun () -> match_ (a x) []);
  rejects "wildcard only" (fun () -> match_ (a x) [ wildcard ]);
  rejects "missing wildcard" (fun () -> match_ (a x) [ nil_case ]);
  rejects "early wildcard" (fun () -> match_ (a x) [ wildcard; nil_case ]);
  rejects "repeated wildcard" (fun () ->
      match_ (a x) [ nil_case; wildcard; wildcard ]);
  rejects "repeated head" (fun () ->
      match_ (a x)
        [ branch P_int [ x ] (t x); branch P_int [ y ] (t y); wildcard ]);
  ignore
    (match_ (a z)
       [
         branch P_int [ x ] (t x);
         branch P_bool [ x ] (t x);
         branch P_id [ x ] (t x);
         nil_case;
         branch P_pair [ x; y ] (t y);
         wildcard;
       ]);
  (* Arity/type agreement belongs to typing, not formation. *)
  ignore (apply (value (fn x (t x))) [ int 1; int 2 ]);
  ignore (let_ x (let_ y (t z) (t y)) (t x))

let free_variables () =
  check_fv "fun" [ y ] (fv_value (fn x (pair_term (a x) (a y))));
  check_fv "fix self and parameters" [ y ]
    (fv_value (fix f [ (x, int_ty) ] int_ty (apply (a f) [ a x; a y ])));
  check_fv "let rhs outside scope" [ x; y ]
    (fv_term (let_ x (t x) (pair_term (a x) (a y))));
  check_fv "Pair branch binders" [ z ]
    (fv_branch (branch P_pair [ x; y ] (apply (a z) [ a x; a y ])));
  check_fv "match scrutinee outside branch scope" [ x; z ]
    (fv_term
       (match_ (a x) [ branch P_int [ x ] (t x); branch P_wildcard [] (t z) ]));
  check_fv "empty branch binders" [ x ] (fv_branch (branch P_nil [] (t x)))

let alpha () =
  check "bound names may differ" (alpha_equal_value (fn x (t x)) (fn y (t y)));
  check "free does not equal bound"
    (not (alpha_equal_value (fn x (t y)) (fn y (t y))));
  check "free names matter" (not (alpha_equal_term (t x) (t y)));
  check "annotations matter"
    (not (alpha_equal_value (fn x (t x)) (fun_ [ (x, bool_ty) ] int_ty (t x))));
  let nested = fn x (atom (value (fn x (t x)))) in
  check "nested shadowing"
    (alpha_equal_value nested (fn y (atom (value (fn z (t z))))));
  check "inner versus outer occurrence"
    (not (alpha_equal_value nested (fn y (atom (value (fn z (t y)))))));
  check "parameter positions"
    (not
       (alpha_equal_value
          (fun_ [ (x, int_ty); (y, int_ty) ] int_ty (t x))
          (fun_ [ (y, int_ty); (x, int_ty) ] int_ty (t x))));
  check "fix self position"
    (alpha_equal_value
       (fix f [ (x, int_ty) ] int_ty (apply (a f) [ a x ]))
       (fix z [ (y, int_ty) ] int_ty (apply (a z) [ a y ])));
  check "branch labels rename with body"
    (alpha_equal_branch
       (branch P_pair [ x; y ] (t x))
       (branch P_pair [ y; z ] (t y)));
  check "let rhs not alpha-bound"
    (not (alpha_equal_term (let_ x (t x) (t x)) (let_ y (t y) (t y))));
  check "branch order is syntax"
    (not
       (alpha_equal_term
          (match_ (a z)
             [
               branch P_nil [] (t z);
               branch P_int [ x ] (t z);
               branch P_wildcard [] (t z);
             ])
          (match_ (a z)
             [
               branch P_int [ x ] (t z);
               branch P_nil [] (t z);
               branch P_wildcard [] (t z);
             ])))

let exchange_and_traversal () =
  let term =
    let_ x
      (async (operation (a y) Add (int 1)))
      (if_
         (value (boolean true))
         (match_ (a y)
            [
              branch P_pair [ x; z ] (apply (a f) [ a x; a z ]);
              branch P_wildcard []
                (pair_term
                   (value (sexp_id (value (identifier (Id.of_string "x")))))
                   (value (sexp_bool (a y))));
            ])
         (atom (value unit)))
  in
  check "exchange is an involution"
    (alpha_equal_term term (exchange_term x y (exchange_term x y term)));
  check "exchange changes free variables"
    (not (alpha_equal_term (t x) (exchange_term x y (t x))));
  check "exchange fixes identifier literals"
    (alpha_equal_value
       (identifier (Id.of_string "x"))
       (exchange_value x y (identifier (Id.of_string "x"))));
  check_fv "traversal before substitution" [ y; f ] (fv_term term);
  check_fv "traversal after substitution" []
    (fv_term
       (subst_term
          (simultaneous [ (y, nil_atom); (f, value (fn u (t u))) ])
          term))

let scope () =
  check "let scope"
    (alpha_equal_term
       (subst_term (single x (int 1)) (let_ x (t x) (t x)))
       (let_ x (atom (int 1)) (t x)));
  let recursive = fix f [ (x, int_ty) ] int_ty (apply (a f) [ a x; a y ]) in
  check "fix shadows self and parameter only"
    (alpha_equal_value
       (subst_value
          (simultaneous [ (f, nil_atom); (x, int 1); (y, int 2) ])
          recursive)
       (fix f [ (x, int_ty) ] int_ty (apply (a f) [ a x; int 2 ])));
  check "match replaces scrutinee and wildcard but not bound occurrence"
    (alpha_equal_term
       (subst_term
          (single x (int 1))
          (match_ (a x)
             [ branch P_int [ x ] (t x); branch P_wildcard [] (t x) ]))
       (match_ (int 1)
          [ branch P_int [ x ] (t x); branch P_wildcard [] (atom (int 1)) ]));
  check "Nil has no binder"
    (alpha_equal_branch
       (subst_branch (single x (int 1)) (branch P_nil [] (t x)))
       (branch P_nil [] (atom (int 1))))

let capture () =
  let substituted = subst_value (single x (a y)) (fn y (t x)) in
  check "fun avoids capture" (alpha_equal_value substituted (fn z (t y)));
  check_fv "inserted y remains free" [ y ] (fv_value substituted);
  check "shadowing a key does not capture another replacement"
    (alpha_equal_value
       (subst_value
          (simultaneous [ (x, nil_atom); (y, a x) ])
          (fn x (pair_term (a x) (a y))))
       (fn u (pair_term (a u) (a x))));
  check "fresh names avoid the substitution domain"
    (alpha_equal_value
       (subst_value
          (simultaneous [ (x, a y); (Var.fresh "y'", a z) ])
          (fn y (pair_term (a x) (a y))))
       (fn u (pair_term (a y) (a u))));
  check "branch avoids capture"
    (alpha_equal_branch
       (subst_branch
          (single z (a x))
          (branch P_pair [ x; y ] (pair_term (a z) (a x))))
       (branch P_pair [ u; y ] (pair_term (a x) (a u))));
  check "fix freshens self as well as parameters"
    (alpha_equal_value
       (subst_value
          (simultaneous [ (y, a f); (z, a x) ])
          (fix f [ (x, sexp_ty) ] sexp_ty (pair_term (a y) (a z))))
       (fix u
          [ (Var.fresh "parameter", sexp_ty) ]
          sexp_ty
          (pair_term (a f) (a x))));
  let nested = fn y (atom (value (fn y (t x)))) in
  check "capture avoidance with nested same names"
    (alpha_equal_value
       (subst_value (single x (a y)) nested)
       (fn z (atom (value (fn u (t y))))));
  let taken = Var.fresh "y'" in
  let body = fn y (let_ taken (t x) (pair_term (a y) (a taken))) in
  check "fresh choice avoids inner binders"
    (alpha_equal_value
       (subst_value (single x (a y)) body)
       (fn z (let_ taken (t y) (pair_term (a z) (a taken)))))

let simultaneous_substitution () =
  let original = pair_term (a x) (a y) in
  let substituted =
    subst_term (simultaneous [ (x, a y); (y, nil_atom) ]) original
  in
  check "simultaneous, not iterated"
    (alpha_equal_term substituted (pair_term (a y) nil_atom));
  check "replacement is inserted unchanged"
    (not (alpha_equal_term substituted (pair_term nil_atom nil_atom)));
  check "simultaneous swap"
    (alpha_equal_term
       (subst_term (simultaneous [ (x, a y); (y, a x) ]) original)
       (pair_term (a y) (a x)));
  check "empty substitution"
    (alpha_equal_term (subst_term empty original) original);
  match simultaneous [ (x, a y); (x, a z) ] with
  | _ -> failwith "duplicate substitution domain accepted"
  | exception Invalid_argument _ -> ()

let () =
  List.iter
    (fun (label, run) ->
      run ();
      Printf.printf "Passed: %s\n" label)
    [
      ("data distinctions", data);
      ("formation", formation);
      ("free variables", free_variables);
      ("alpha-equivalence", alpha);
      ("exchange and traversal", exchange_and_traversal);
      ("binding scope", scope);
      ("capture avoidance", capture);
      ("simultaneous substitution", simultaneous_substitution);
    ]

open Source_calculus
module Frontend = Source_frontend.Frontend

let read ?(free = []) text =
  match Frontend.toplevel ~free (Lexing.from_string text) with
  | Ok command -> command.Zoo.data
  | Error (_, message) -> failwith (text ^ ": " ^ message)

let rejects text =
  match Frontend.toplevel (Lexing.from_string text) with
  | Error _ -> ()
  | Ok _ -> failwith ("Accepted invalid syntax: " ^ text)

let evaluate text =
  let term = read text in
  ignore (Typing.type_term Syntax.Var.Map.empty term);
  let rec run remaining term =
    match Reduction.step term with
    | Some (_, next) when remaining > 0 -> run (remaining - 1) next
    | Some _ -> failwith "Example exceeded its check bound"
    | None -> (
        match term with
        | Syntax.Atom (Syntax.Value _) -> Format.asprintf "%a" Print.term term
        | _ -> failwith "Example got stuck")
  in
  run 100 term

let () =
  List.iter
    (fun (text, expected) ->
      let actual = evaluate text in
      if actual <> expected then failwith (text ^ " evaluated to " ^ actual))
    [
      ("let x = async (1+2) in x+3", "6");
      ("let x = let y = 1 in y in x", "1");
      ("let f = fun (x : int) : int is x in f(-2)", "-2");
      ( "let f = fun (g : (int) -> int, x : int) : int is g(x) in\n\
         f(fun (y : int) : int is y, 42)",
        "42" );
      ( "let down = fix f(n : int) : int is let b = n < 1 in\n\
         if b then 0 else let m = n-1 in f(m) in down(3)",
        "0" );
      ("match Pair(Int(1), Nil) { Pair(x,y) => x | _ => Nil }", "Int(1)");
      ("match Bool(false) { Bool(x) ⇒ x | _ => true }", "false");
      ("match Id(\"C\") { Id(x) => x | _ => \"?\" }", "\"C\"");
      ("match Int(-1) { Int(x) => x | _ => 0 }", "-1");
      ("match Nil { Nil => () | _ => () }", "()");
      ("match Nil { Int(x) => 1 | _ => 2 }", "2");
      ("18446744073709551616+1", "18446744073709551617");
      ("\"a\\\"b\\n\" = \"a\\034b\\010\"", "true");
      ("(* outer\n (* nested *) *) if true then -1 else 0;;", "-1");
    ];
  (* Parsing must not silently name, evaluate, or accept non-atomic operands. *)
  List.iter rejects
    [
      "f(1+2)";
      "(f(x)) + 1";
      "1+2+3";
      "if 1<2 then 0 else 1";
      "Pair(async Nil, Nil)";
      "match async Nil { Nil => 0 | _ => 1 }";
      "f()";
      "fun () : int is 1";
      "fun (x:int,x:int) : int is x";
      "fix f(f:int) : int is f";
      "match Nil { Pair(x,x) => x | _ => Nil }";
      "match Nil { Nil => 0 }";
      "match Nil { _ => 0 }";
      "match Nil { _ => 0 | Nil => 1 }";
      "match Nil { Nil => 0 | Nil => 1 | _ => 2 }";
      "let x = 1;;";
      "(* unfinished";
      "\"unfinished";
      "\"\\q\"";
      "@";
    ];
  (* Parsing does not replace typing. *)
  (match Typing.type_term Syntax.Var.Map.empty (read "1 + true") with
  | _ -> failwith "Accepted an ill-typed term"
  | exception Typing.Type_error _ -> ());
  (match Frontend.file (Lexing.from_string "1;; true;; ()") with
  | [ Ok _; Ok _; Ok _ ] -> ()
  | _ -> failwith "File command separation");
  (match Frontend.file (Lexing.from_string "") with
  | [] -> ()
  | _ -> failwith "Empty file");
  List.iter
    (fun text ->
      let term = read text in
      let displayed = Format.asprintf "%a" Print.term term in
      if not (Binding.alpha_equal_term term (read displayed)) then
        failwith ("Printing changed syntax: " ^ displayed))
    [
      "let x = async (1+2) in x+3";
      "fun (f:(int)->bool) : (int)->bool is f";
      "match Pair(Int(1), Nil) { Pair(x,y) => x | _ => Nil }";
    ];
  (* Representation migration: compare binding structure, not display hints. *)
  let open Syntax in
  let x = Var.fresh "x" and other_x = Var.fresh "x" in
  if Var.equal x other_x then failwith "Same hint merged variable identities";
  let scoped = read ~free:[ ("x", x) ] "let x = x in x" in
  (match scoped with
  | Let (rhs, body) ->
      if not (Binding.alpha_equal_term rhs (atom (variable x))) then
        failwith "Let binder entered RHS scope";
      if
        not
          (Binding.alpha_equal_term
             (Bindlib.subst body (variable other_x))
             (atom (variable other_x)))
      then failwith "Let occurrence did not use its binder"
  | _ -> failwith "Expected let");
  if not (Var.Set.equal (Binding.fv_term scoped) (Var.Set.singleton x)) then
    failwith "Let changed free identities";
  let open_term = read ~free:[ ("x", x) ] "x + x" in
  if
    not
      (Binding.alpha_equal_term open_term
         (operation (variable x) Add (variable x)))
  then failwith "Repeated free name did not resolve consistently";
  if Var.Set.cardinal (Binding.fv_term (read "x + x")) <> 1 then
    failwith "Default free-name table did not share occurrences";
  if Binding.alpha_equal_term (read "x") (read "x") then
    failwith "Independent commands shared implicit identities";
  List.iter
    (fun free ->
      match Frontend.toplevel ~free (Lexing.from_string "x") with
      | Error _ -> ()
      | Ok _ -> failwith "Ambiguous free-name association accepted")
    [ [ ("x", x); ("x", other_x) ]; [ ("x", x); ("y", x) ] ];
  let y = Var.fresh "y" in
  let captured =
    Binding.subst_term
      (Binding.single x (variable y))
      (read ~free:[ ("x", x) ] "fun (y:int):int is x")
  in
  let shown = Format.asprintf "%a" Print.term captured in
  if not (Binding.alpha_equal_term captured (read ~free:[ ("y", y) ] shown))
  then failwith ("Printing captured free y: " ^ shown);
  List.iter
    (fun text ->
      let term = read text in
      let shown = Format.asprintf "%a" Print.term term in
      if not (Binding.alpha_equal_term term (read shown)) then
        failwith ("Round trip changed binding: " ^ shown))
    [
      "fun (x:int):int is let x = x in x";
      "fix f(x:int):int is let f = fun (x:int):int is x in f(x)";
      "fun (x:sexp):sexp is match x { Pair(x,y) => y | _ => x }";
    ];
  let keyword = Var.fresh "let" in
  let term =
    atom (value (fun_ [ (keyword, int_ty) ] int_ty (atom (variable keyword))))
  in
  if
    not
      (Binding.alpha_equal_term term
         (read (Format.asprintf "%a" Print.term term)))
  then failwith "Reserved binder hint did not round trip";
  (* Resolver failures retain the offending command's location in a file. *)
  let input = Lexing.from_string "fun (x:int,x:int):int is x;;\n1" in
  input.Lexing.lex_curr_p <-
    { input.Lexing.lex_curr_p with pos_fname = "input.async" };
  (match Frontend.file input with
  | [ Error (loc, _) ]
    when String.starts_with ~prefix:"file \"input.async\", line 1,"
           (Format.asprintf "%t" (Zoo.print_location loc)) ->
      ()
  | _ -> failwith "Formation error lost its command location");
  print_endline "Passed source text parsing, formation, and evaluation"

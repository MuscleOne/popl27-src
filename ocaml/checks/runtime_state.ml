open Runtime_calculus
open Runtime_syntax
module State = Runtime_state

let check label condition = if not condition then failwith label
let p = FName.of_z Z.zero
let q = FName.of_z Z.one
let r = FName.of_z (Z.of_int 2)
let name p = atom (value (future p))
let number n = atom (value (integer (Z.of_int n)))
let empty = FName.Map.empty
let signature = FName.Map.(empty |> add p int_ty |> add q int_ty)

let rejects label build =
  match build () with
  | _ -> failwith (label ^ ": accepted unformed state")
  | exception State.Invalid_state _ -> ()

let formation_and_finality () =
  rejects "mapping key outside signature" (fun () ->
      State.make empty (number 0) (FName.Map.singleton p (number 1)));
  rejects "future in focus outside signature" (fun () ->
      State.make signature (name r) empty);
  let x = Var.fresh "x" in
  rejects "future under mapped binder outside signature" (fun () ->
      State.make signature (number 0)
        (FName.Map.singleton p
           (atom (value (fun_ [ (x, int_ty) ] int_ty (name r))))));
  let incomplete = State.make signature (name p) empty in
  check "finality does not demand entries for every declaration" (State.final incomplete);
  let open_term = atom (variable x) in
  check "formed source variable is not a value"
    (not (State.final (State.make empty open_term empty)));
  let open_value = atom (value (sexp_bool (variable x))) in
  check "formation/finality do not imply closure or typing"
    (State.final (State.make empty open_value empty));
  let pending = async (number 1) in
  check "non-value focus" (not (State.final (State.make empty pending empty)));
  check "pending mapped term despite value focus"
    (not (State.final (State.make signature (number 0) (FName.Map.singleton p pending))));
  let aliases = FName.Map.(empty |> add p (name q) |> add q (name p)) in
  check "alias cycle consists of returned values"
    (State.final (State.make signature (name p) aliases));
  check "future fields need no dereference for finality"
    (State.final (State.make signature
       (atom (value (pair (value (future p)) (value nil)))) aliases))

let equality_and_names () =
  let x = Var.fresh "x" and y = Var.fresh "y" in
  let fn x = atom (value (fun_ [ (x, int_ty) ] int_ty (atom (variable x)))) in
  let left = State.make signature (fn x)
      FName.Map.(empty |> add p (number 1) |> add q (number 2)) in
  let right = State.make FName.Map.(empty |> add q int_ty |> add p int_ty) (fn y)
      FName.Map.(empty |> add q (number 2) |> add p (number 1)) in
  check "maps extensional, binders alpha-equivalent" (State.equal left right);
  let fn_with_future =
    atom (value (fun_ [ (x, int_ty) ] int_ty (name p)))
  in
  let original = State.make signature fn_with_future
      FName.Map.(empty |> add p (name q) |> add q (name p)) in
  let renamed = State.exchange_futures p r original in
  let expected = State.make FName.Map.(empty |> add r int_ty |> add q int_ty)
      (atom (value (fun_ [ (x, int_ty) ] int_ty (name r))))
      FName.Map.(empty |> add r (name q) |> add q (name r)) in
  check "rename declarations, keys and bound-body occurrences"
    (State.equal renamed expected);
  check "state equality retains future names" (not (State.equal original renamed));
  check "transposition involution"
    (State.equal original (State.exchange_futures p r renamed));
  let swapped = State.exchange_futures p q left in
  check "swapping allocated keys preserves both entries"
    (State.equal swapped (State.make signature (fn y)
       FName.Map.(empty |> add p (number 2) |> add q (number 1))));
  check "fresh even for an allocated name with no mapping entry"
    (not (FName.Set.mem (State.fresh signature) (State.domain signature)));
  let huge = FName.of_z (Z.of_string "184467440737095516160000000000000000001") in
  check "fresh without machine-integer overflow"
    (FName.compare (State.fresh (FName.Map.singleton huge int_ty)) huge > 0)

let printing () =
  let x = Var.fresh "x" in
  let other_x = Var.fresh "x" in
  let state = State.make signature (atom (variable x))
      FName.Map.(empty |> add p (atom (variable other_x)) |> add q (atom (variable x))) in
  let text = Format.asprintf "%a" Runtime_print.state state in
  let text =
    String.map (function '\n' -> ' ' | c -> c) text
    |> String.split_on_char ' ' |> List.filter (( <> ) "") |> String.concat " "
  in
  check ("one naming context across state: " ^ text)
    (text = "nu [future(0) ~ int, future(1) ~ int] { x1 || [future(0) := x, future(1) := x1] }");
  check "printing preserves variable identities"
    (Runtime_binding.alpha_equal_term state.focus (atom (variable x)))

let () =
  formation_and_finality ();
  equality_and_names ();
  printing ();
  print_endline "Runtime state checks passed"

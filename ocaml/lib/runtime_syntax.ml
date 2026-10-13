(* runtime-calculus.md, sections 1--3. No source evaluator or runtime state. *)
include Common_syntax

let require condition message =
  if not condition then raise (Invalid_syntax message)

module FName = struct
  type t = Z.t

  let of_z n =
    require (Z.sign n >= 0) "A future-name index must be non-negative";
    n

  let to_z n = n
  let equal = Z.equal
  let compare = Z.compare

  module Set = Set.Make (Z)
  module Map = Map.Make (Z)
end

(* Field variables are stored by the branch binder, not duplicated in patterns. *)
type pattern_head = P_int | P_bool | P_id | P_nil | P_pair | P_wildcard

type value =
  | Integer of Z.t
  | Boolean of bool
  | Unit
  | Identifier of Id.t
  | Future of FName.t
  | Fun of ty list * ty * (atom, term) Bindlib.mbinder
  | Fix of ty list * ty * (atom, term) Bindlib.mbinder
  | Sexp_int of atom
  | Sexp_bool of atom
  | Sexp_id of atom
  | Nil
  | Pair of atom * atom

and atom = Variable of atom Bindlib.var | Value of value

and term =
  | Atom of atom
  | Apply of atom * atom list
  | Operation of atom * op * atom
  | If of atom * term * term
  | Let of term * (atom, term) Bindlib.binder
  | Match of atom * branch list
  | Async of term

and branch = Branch of pattern_head * (atom, term) Bindlib.mbinder

type variable = atom Bindlib.var
type parameter = variable * ty

module Var = struct
  type t = variable

  let fresh name = Bindlib.new_var (fun x -> Variable x) name
  let name = Bindlib.name_of
  let equal = Bindlib.eq_vars
  let compare (x : t) (y : t) = Bindlib.compare_vars x y

  module Ordered = struct
    type nonrec t = t

    let compare = compare
  end

  module Set = Set.Make (Ordered)
  module Map = Map.Make (Ordered)
end

(* Every variable occurrence must enter through box_var. Public constructors
   accept finished syntax and use these traversals before binding it. *)
let rec box_value = function
  | (Integer _ | Boolean _ | Unit | Identifier _ | Future _ | Nil) as w ->
      Bindlib.box w
  | Fun (types, result, body) ->
      Bindlib.box_apply
        (fun body -> Fun (types, result, body))
        (Bindlib.box_mbinder box_term body)
  | Fix (types, result, body) ->
      Bindlib.box_apply
        (fun body -> Fix (types, result, body))
        (Bindlib.box_mbinder box_term body)
  | Sexp_int b -> Bindlib.box_apply (fun b -> Sexp_int b) (box_atom b)
  | Sexp_bool b -> Bindlib.box_apply (fun b -> Sexp_bool b) (box_atom b)
  | Sexp_id b -> Bindlib.box_apply (fun b -> Sexp_id b) (box_atom b)
  | Pair (a, b) ->
      Bindlib.box_apply2 (fun a b -> Pair (a, b)) (box_atom a) (box_atom b)

and box_atom = function
  | Variable x -> Bindlib.box_var x
  | Value w -> Bindlib.box_apply (fun w -> Value w) (box_value w)

and box_term = function
  | Atom b -> Bindlib.box_apply (fun b -> Atom b) (box_atom b)
  | Apply (fn, args) ->
      Bindlib.box_apply2
        (fun fn args -> Apply (fn, args))
        (box_atom fn)
        (Bindlib.box_list (List.map box_atom args))
  | Operation (a, op, b) ->
      Bindlib.box_apply2
        (fun a b -> Operation (a, op, b))
        (box_atom a) (box_atom b)
  | If (guard, yes, no) ->
      Bindlib.box_apply3
        (fun g y n -> If (g, y, n))
        (box_atom guard) (box_term yes) (box_term no)
  | Let (rhs, body) ->
      Bindlib.box_apply2
        (fun rhs body -> Let (rhs, body))
        (box_term rhs)
        (Bindlib.box_binder box_term body)
  | Match (scrutinee, branches) ->
      Bindlib.box_apply2
        (fun s bs -> Match (s, bs))
        (box_atom scrutinee)
        (Bindlib.box_list (List.map box_branch branches))
  | Async body -> Bindlib.box_apply (fun body -> Async body) (box_term body)

and box_branch (Branch (pat, body)) =
  Bindlib.box_apply
    (fun body -> Branch (pat, body))
    (Bindlib.box_mbinder box_term body)

let require_distinct variables =
  let rec check seen = function
    | [] -> ()
    | x :: rest ->
        require
          (not (Var.Set.mem x seen))
          "Variables in one binder must be distinct";
        check (Var.Set.add x seen) rest
  in
  check Var.Set.empty variables

let bind variables body =
  require_distinct variables;
  Bindlib.unbox (Bindlib.bind_mvar (Array.of_list variables) (box_term body))

let integer n = Integer n
let boolean b = Boolean b
let unit = Unit
let identifier name = Identifier name
let future p = Future p

let fun_ parameters result body =
  require (parameters <> []) "A function needs at least one parameter";
  Fun (List.map snd parameters, result, bind (List.map fst parameters) body)

let fix self parameters result body =
  require (parameters <> []) "A recursive function needs at least one parameter";
  Fix
    ( List.map snd parameters,
      result,
      bind (self :: List.map fst parameters) body )

let sexp_int a = Sexp_int a
let sexp_bool a = Sexp_bool a
let sexp_id a = Sexp_id a
let nil = Nil
let pair a b = Pair (a, b)
let variable x = Variable x
let value w = Value w
let atom b = Atom b

let apply fn arguments =
  require (arguments <> []) "An application needs at least one argument";
  Apply (fn, arguments)

let operation a op b = Operation (a, op, b)
let if_ g y n = If (g, y, n)

let let_ x rhs body =
  Let (rhs, Bindlib.unbox (Bindlib.bind_var x (box_term body)))

let branch pattern variables body =
  let arity =
    match pattern with
    | P_int | P_bool | P_id -> 1
    | P_pair -> 2
    | P_nil | P_wildcard -> 0
  in
  require
    (List.length variables = arity)
    "Pattern field count does not match its constructor";
  Branch (pattern, bind variables body)

let match_ scrutinee branches =
  let rec check seen = function
    | [ Branch (P_wildcard, _) ] ->
        require (seen <> []) "A match needs at least one constructor branch"
    | Branch (P_wildcard, _) :: _ ->
        raise
          (Invalid_syntax "A match has exactly one wildcard, in last position")
    | Branch (pat, _) :: rest ->
        require
          (not (List.mem pat seen))
          "Constructor heads in a match must be distinct";
        check (pat :: seen) rest
    | [] -> raise (Invalid_syntax "A match must end with a wildcard branch")
  in
  check [] branches;
  Match (scrutinee, branches)

let async body = Async body

(* Unbinding only freshens variables. Future identities and U are unchanged. *)
let rec formed_value active = function
  | Integer _ | Boolean _ | Unit | Identifier _ | Nil -> true
  | Future p -> FName.Set.mem p active
  | Fun (_, _, body) | Fix (_, _, body) ->
      let _, body = Bindlib.unmbind body in
      formed_term active body
  | Sexp_int b | Sexp_bool b | Sexp_id b -> formed_atom active b
  | Pair (a, b) -> formed_atom active a && formed_atom active b

and formed_atom active = function
  | Variable _ -> true
  | Value w -> formed_value active w

and formed_term active = function
  | Atom b -> formed_atom active b
  | Apply (fn, args) ->
      formed_atom active fn && List.for_all (formed_atom active) args
  | Operation (a, _, b) -> formed_atom active a && formed_atom active b
  | If (g, y, n) ->
      formed_atom active g && formed_term active y && formed_term active n
  | Let (rhs, body) ->
      let _, body = Bindlib.unbind body in
      formed_term active rhs && formed_term active body
  | Match (s, bs) ->
      formed_atom active s && List.for_all (formed_branch active) bs
  | Async body -> formed_term active body

and formed_branch active (Branch (_, body)) =
  let _, body = Bindlib.unmbind body in
  formed_term active body

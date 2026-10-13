open Syntax
open Format

let comma ppf () = fprintf ppf ",@ "
let list print = pp_print_list ~pp_sep:comma print

let variable ppf x =
  let name = Var.name x in
  let letter = function 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false in
  let character c =
    letter c || match c with '0' .. '9' | '\'' -> true | _ -> false
  in
  if name <> "" && letter name.[0] && String.for_all character name then
    pp_print_string ppf name
  else fprintf ppf "var(%S)" name

let rec ty ppf = function
  | Ty_int -> pp_print_string ppf "int"
  | Ty_bool -> pp_print_string ppf "bool"
  | Ty_unit -> pp_print_string ppf "unit"
  | Ty_id -> pp_print_string ppf "id"
  | Ty_sexp -> pp_print_string ppf "sexp"
  | Ty_arrow (parameters, result) ->
      fprintf ppf "@[<hov 2>(%a) ->@ %a@]" (list ty) parameters ty result

let parameter ppf (x, annotation) =
  fprintf ppf "@[<hov 2>%a :@ %a@]" variable x ty annotation

let op ppf = function
  | Add -> pp_print_string ppf "+"
  | Sub -> pp_print_string ppf "-"
  | Mul -> pp_print_string ppf "*"
  | Eq -> pp_print_string ppf "="
  | Lt -> pp_print_string ppf "<"

let rec value_in ctxt ppf = function
  | Integer n -> pp_print_string ppf (Z.to_string n)
  | Boolean b -> pp_print_bool ppf b
  | Unit -> pp_print_string ppf "()"
  | Identifier name -> fprintf ppf "%S" (Id.to_string name)
  | Fun (types, result, body) ->
      let xs, body, ctxt = Bindlib.unmbind_in ctxt body in
      let parameters = List.combine (Array.to_list xs) types in
      fprintf ppf "@[<hov 2>(fun (%a) : %a is@ %a)@]" (list parameter)
        parameters ty result (term_in ctxt) body
  | Fix (types, result, body) ->
      let xs, body, ctxt = Bindlib.unmbind_in ctxt body in
      let self = xs.(0) in
      let parameters =
        List.combine
          (Array.to_list (Array.sub xs 1 (Array.length xs - 1)))
          types
      in
      fprintf ppf "@[<hov 2>(fix %a(%a) : %a is@ %a)@]" variable self
        (list parameter) parameters ty result (term_in ctxt) body
  | Sexp_int a -> fprintf ppf "@[<hov 2>Int(%a)@]" (atom_in ctxt) a
  | Sexp_bool a -> fprintf ppf "@[<hov 2>Bool(%a)@]" (atom_in ctxt) a
  | Sexp_id a -> fprintf ppf "@[<hov 2>Id(%a)@]" (atom_in ctxt) a
  | Nil -> pp_print_string ppf "Nil"
  | Pair (a, b) ->
      fprintf ppf "@[<hov 2>Pair(%a,@ %a)@]" (atom_in ctxt) a (atom_in ctxt) b

and atom_in ctxt ppf = function
  | Variable x -> variable ppf x
  | Value v -> value_in ctxt ppf v

and term_in ctxt ppf = function
  | Atom a -> atom_in ctxt ppf a
  | Apply (fn, arguments) ->
      fprintf ppf "@[<hov 2>%a(%a)@]" (atom_in ctxt) fn
        (list (atom_in ctxt))
        arguments
  | Operation (a, operator, b) ->
      fprintf ppf "@[<hov 2>%a %a@ %a@]" (atom_in ctxt) a op operator
        (atom_in ctxt) b
  | If (guard, yes, no) ->
      fprintf ppf "@[<hov 2>if %a then@ (%a)@ else@ (%a)@]" (atom_in ctxt) guard
        (term_in ctxt) yes (term_in ctxt) no
  | Let (rhs, binding) ->
      let x, body, inner = Bindlib.unbind_in ctxt binding in
      fprintf ppf "@[<hov 2>let %a = (%a) in@ %a@]" variable x (term_in ctxt)
        rhs (term_in inner) body
  | Match (scrutinee, branches) ->
      let separator ppf () = fprintf ppf "@ | " in
      fprintf ppf "@[<hov 2>match %a {@ %a@ }@]" (atom_in ctxt) scrutinee
        (pp_print_list ~pp_sep:separator (branch_in ctxt))
        branches
  | Async body -> fprintf ppf "@[<hov 2>async (%a)@]" (term_in ctxt) body

and branch_in ctxt ppf (Branch (pat, binding)) =
  let xs, body, ctxt = Bindlib.unmbind_in ctxt binding in
  let pattern ppf () =
    match pat with
    | P_int -> fprintf ppf "Int(%a)" variable xs.(0)
    | P_bool -> fprintf ppf "Bool(%a)" variable xs.(0)
    | P_id -> fprintf ppf "Id(%a)" variable xs.(0)
    | P_nil -> pp_print_string ppf "Nil"
    | P_pair -> fprintf ppf "@[Pair(%a,@ %a)@]" variable xs.(0) variable xs.(1)
    | P_wildcard -> pp_print_string ppf "_"
  in
  fprintf ppf "@[<hov 2>%a =>@ %a@]" pattern () (term_in ctxt) body

(* Give even distinct free variables with the same preferred name distinct
   printable names. This changes a temporary display copy, not the input term. *)
let keywords =
  [
    "fun";
    "fix";
    "is";
    "let";
    "in";
    "if";
    "then";
    "else";
    "async";
    "match";
    "int";
    "bool";
    "unit";
    "id";
    "sexp";
    "true";
    "false";
    "Int";
    "Bool";
    "Id";
    "Nil";
    "Pair";
    "_";
  ]

let display fv subst print ppf phrase =
  let initial =
    List.fold_left
      (fun c s -> Bindlib.reserve_name s c)
      Bindlib.empty_ctxt keywords
  in
  let ctxt, entries =
    Var.Set.fold
      (fun x (ctxt, entries) ->
        let y, ctxt = Bindlib.new_var_in ctxt Syntax.variable (Var.name x) in
        (ctxt, (x, Syntax.variable y) :: entries))
      (fv phrase) (initial, [])
  in
  let phrase = subst (Binding.simultaneous entries) phrase in
  print ctxt ppf phrase

let value = display Binding.fv_value Binding.subst_value value_in
let atom = display Binding.fv_atom Binding.subst_atom atom_in
let term = display Binding.fv_term Binding.subst_term term_in
let branch = display Binding.fv_branch Binding.subst_branch branch_in

let error ppf = function
  | Typing.Unbound_variable x -> fprintf ppf "Unbound variable %a" variable x
  | Typing.Type_mismatch { rule; expected; actual } ->
      fprintf ppf "@[<hov 2>%s: expected %a,@ found %a@]" rule ty expected ty
        actual
  | Typing.Not_function actual ->
      fprintf ppf "@[<hov 2>Application expects a function,@ found %a@]" ty
        actual
  | Typing.Arity_mismatch { expected; actual } ->
      fprintf ppf "@[<hov 2>Application expects %d argument(s),@ found %d@]"
        expected actual
  | Typing.Equality_type actual ->
      fprintf ppf "@[<hov 2>Equality expects int or id operands,@ found %a@]" ty
        actual

let rec rule ppf = function
  | Reduction.Search_let inner as outer ->
      fprintf ppf "%s(%a)" (Reduction.rule_name outer) rule inner
  | other -> pp_print_string ppf (Reduction.rule_name other)

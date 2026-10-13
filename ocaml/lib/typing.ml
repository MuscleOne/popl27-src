(* source-calculus.md section 6; rule tags accompany checks or base cases. *)
open Syntax

type environment = ty Var.Map.t

type error =
  | Unbound_variable of Var.t
  | Type_mismatch of { rule : string; expected : ty; actual : ty }
  | Not_function of ty
  | Arity_mismatch of { expected : int; actual : int }
  | Equality_type of ty

exception Type_error of error

let require_type rule expected actual =
  if not (equal_ty expected actual) then
    raise (Type_error (Type_mismatch { rule; expected; actual }))

(* Gamma,x:tau is a persistent finite-map update, including shadowing. *)
let extend environment parameters =
  List.fold_left
    (fun environment (x, ty) -> Var.Map.add x ty environment)
    environment parameters

let rec type_value environment = function
  | Integer _ -> int_ty (* T-Int *)
  | Boolean _ -> bool_ty (* T-True, T-False *)
  | Unit -> unit_ty (* T-Unit *)
  | Identifier _ -> id_ty (* T-Id *)
  | Fun (types, result, binding) ->
      let xs, body = Bindlib.unmbind binding in
      let parameters = List.combine (Array.to_list xs) types in
      require_type "T-Fun" result
        (type_term (extend environment parameters) body);
      arrow types result
  | Fix (types, result, binding) ->
      let xs, body = Bindlib.unmbind binding in
      let fn_type = arrow types result in
      let parameters = List.combine (Array.to_list xs) (fn_type :: types) in
      require_type "T-Fix" result
        (type_term (extend environment parameters) body);
      fn_type
  | Sexp_int a ->
      require_type "T-Constructor-Int" int_ty (type_atom environment a);
      sexp_ty
  | Sexp_bool a ->
      require_type "T-Constructor-Bool" bool_ty (type_atom environment a);
      sexp_ty
  | Sexp_id a ->
      require_type "T-Constructor-Id" id_ty (type_atom environment a);
      sexp_ty
  | Nil -> sexp_ty (* T-Constructor-Nil *)
  | Pair (a, b) ->
      require_type "T-Constructor-Pair" sexp_ty (type_atom environment a);
      require_type "T-Constructor-Pair" sexp_ty (type_atom environment b);
      sexp_ty

and type_atom environment = function
  | Variable x -> (
      (* T-Var *)
      match Var.Map.find_opt x environment with
      | Some ty -> ty
      | None -> raise (Type_error (Unbound_variable x)))
  | Value v -> type_value environment v

and type_term environment = function
  | Atom a -> type_atom environment a
  | Apply (fn, arguments) -> (
      match type_atom environment fn with
      | Ty_arrow (parameters, result) ->
          let expected = List.length parameters
          and actual = List.length arguments in
          if expected <> actual then
            raise (Type_error (Arity_mismatch { expected; actual }));
          List.iter2
            (fun expected argument ->
              require_type "T-App" expected (type_atom environment argument))
            parameters arguments;
          result
      | actual -> raise (Type_error (Not_function actual)))
  | Operation (a, (Add | Sub | Mul), b) ->
      require_type "T-Arith" int_ty (type_atom environment a);
      require_type "T-Arith" int_ty (type_atom environment b);
      int_ty
  | Operation (a, Lt, b) ->
      require_type "T-Lt" int_ty (type_atom environment a);
      require_type "T-Lt" int_ty (type_atom environment b);
      bool_ty
  | Operation (a, Eq, b) ->
      let operand_type = type_atom environment a in
      (match operand_type with
      | Ty_int | Ty_id -> ()
      | _ -> raise (Type_error (Equality_type operand_type)));
      require_type "T-Eq" operand_type (type_atom environment b);
      bool_ty
  | If (guard, yes, no) ->
      require_type "T-If" bool_ty (type_atom environment guard);
      let result = type_term environment yes in
      require_type "T-If" result (type_term environment no);
      result
  | Let (rhs, binding) ->
      (* T-Let: the binder is not in scope in rhs. *)
      let bound_type = type_term environment rhs in
      let x, body = Bindlib.unbind binding in
      type_term (Var.Map.add x bound_type environment) body
  | Async body -> type_term environment body (* T-Async *)
  | Match (scrutinee, branches) -> (
      (* T-Match: check every branch, including the wildcard. *)
      require_type "T-Match" sexp_ty (type_atom environment scrutinee);
      match branches with
      | first :: rest ->
          let result = type_branch environment first in
          List.iter
            (fun branch ->
              require_type "T-Match" result (type_branch environment branch))
            rest;
          result
      | [] ->
          (* Syntax.match_ guarantees a nonempty branch list. *)
          assert false)

and type_branch environment (Branch (pattern, binding)) =
  let xs, body = Bindlib.unmbind binding in
  let types =
    match pattern with
    | P_int -> [ int_ty ] (* T-Branch-Int *)
    | P_bool -> [ bool_ty ] (* T-Branch-Bool *)
    | P_id -> [ id_ty ] (* T-Branch-Id *)
    | P_nil -> [] (* T-Branch-Nil *)
    | P_pair -> [ sexp_ty; sexp_ty ] (* T-Branch-Pair *)
    | P_wildcard -> [] (* T-Branch-Wildcard *)
  in
  type_term (extend environment (List.combine (Array.to_list xs) types)) body

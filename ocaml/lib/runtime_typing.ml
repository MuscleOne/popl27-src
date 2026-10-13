(* runtime-calculus.md sections 4--5. The recursive checks follow Typing,
   using the independent runtime AST and a future signature throughout. *)
open Runtime_syntax

type environment = ty Var.Map.t

type error =
  | Unbound_variable of Var.t
  | Unbound_future of FName.t
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

let rec type_value signature environment = function
  | Integer _ -> int_ty (* T-Int *)
  | Boolean _ -> bool_ty (* T-True, T-False *)
  | Unit -> unit_ty (* T-Unit *)
  | Identifier _ -> id_ty (* T-Id *)
  | Future p -> (
      (* T-Future inspects only Sigma, never a mapping or a future's contents. *)
      match FName.Map.find_opt p signature with
      | Some ty -> ty
      | None -> raise (Type_error (Unbound_future p)))
  | Fun (types, result, binding) ->
      let xs, body = Bindlib.unmbind binding in
      let parameters = List.combine (Array.to_list xs) types in
      require_type "T-Fun" result
        (type_term signature (extend environment parameters) body);
      arrow types result
  | Fix (types, result, binding) ->
      let xs, body = Bindlib.unmbind binding in
      let fn_type = arrow types result in
      let parameters = List.combine (Array.to_list xs) (fn_type :: types) in
      require_type "T-Fix" result
        (type_term signature (extend environment parameters) body);
      fn_type
  | Sexp_int a ->
      require_type "T-Constructor-Int" int_ty
        (type_atom signature environment a);
      sexp_ty
  | Sexp_bool a ->
      require_type "T-Constructor-Bool" bool_ty
        (type_atom signature environment a);
      sexp_ty
  | Sexp_id a ->
      require_type "T-Constructor-Id" id_ty (type_atom signature environment a);
      sexp_ty
  | Nil -> sexp_ty (* T-Constructor-Nil *)
  | Pair (a, b) ->
      require_type "T-Constructor-Pair" sexp_ty
        (type_atom signature environment a);
      require_type "T-Constructor-Pair" sexp_ty
        (type_atom signature environment b);
      sexp_ty

and type_atom signature environment = function
  | Variable x -> (
      (* T-Var *)
      match Var.Map.find_opt x environment with
      | Some ty -> ty
      | None -> raise (Type_error (Unbound_variable x)))
  | Value v -> type_value signature environment v

and type_term signature environment = function
  | Atom a -> type_atom signature environment a
  | Apply (fn, arguments) -> (
      match type_atom signature environment fn with
      | Ty_arrow (parameters, result) ->
          let expected = List.length parameters
          and actual = List.length arguments in
          if expected <> actual then
            raise (Type_error (Arity_mismatch { expected; actual }));
          List.iter2
            (fun expected argument ->
              require_type "T-App" expected
                (type_atom signature environment argument))
            parameters arguments;
          result
      | actual -> raise (Type_error (Not_function actual)))
  | Operation (a, (Add | Sub | Mul), b) ->
      require_type "T-Arith" int_ty (type_atom signature environment a);
      require_type "T-Arith" int_ty (type_atom signature environment b);
      int_ty
  | Operation (a, Lt, b) ->
      require_type "T-Lt" int_ty (type_atom signature environment a);
      require_type "T-Lt" int_ty (type_atom signature environment b);
      bool_ty
  | Operation (a, Eq, b) ->
      let operand_type = type_atom signature environment a in
      (match operand_type with
      | Ty_int | Ty_id -> ()
      | _ -> raise (Type_error (Equality_type operand_type)));
      require_type "T-Eq" operand_type (type_atom signature environment b);
      bool_ty
  | If (guard, yes, no) ->
      require_type "T-If" bool_ty (type_atom signature environment guard);
      let result = type_term signature environment yes in
      require_type "T-If" result (type_term signature environment no);
      result
  | Let (rhs, binding) ->
      (* T-Let: the binder is not in scope in rhs. *)
      let bound_type = type_term signature environment rhs in
      let x, body = Bindlib.unbind binding in
      type_term signature (Var.Map.add x bound_type environment) body
  | Async body -> type_term signature environment body (* T-Async *)
  | Match (scrutinee, branches) -> (
      (* T-Match: check every branch, including the wildcard. *)
      require_type "T-Match" sexp_ty (type_atom signature environment scrutinee);
      match branches with
      | first :: rest ->
          let result = type_branch signature environment first in
          List.iter
            (fun branch ->
              require_type "T-Match" result
                (type_branch signature environment branch))
            rest;
          result
      | [] ->
          (* Runtime_syntax.match_ guarantees a nonempty branch list. *)
          assert false)

and type_branch signature environment (Branch (pattern, binding)) =
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
  type_term signature
    (extend environment (List.combine (Array.to_list xs) types))
    body

type state_error =
  | Domain_mismatch
  | Focus_type_error of error
  | Entry_type_error of FName.t * error

exception State_error of state_error

let check_state (state : Runtime_state.t) =
  (* State-Ok has exactly these three premises. Formation is supplied by t. *)
  if
    not
      (FName.Set.equal
         (Runtime_state.domain state.signature)
         (Runtime_state.domain state.mapping))
  then raise (State_error Domain_mismatch);
  let focus_type =
    try type_term state.signature Var.Map.empty state.focus
    with Type_error error -> raise (State_error (Focus_type_error error))
  in
  FName.Map.iter
    (fun p body ->
      try
        require_type "State-Ok"
          (FName.Map.find p state.signature)
          (type_term state.signature Var.Map.empty body)
      with Type_error error ->
        raise (State_error (Entry_type_error (p, error))))
    state.mapping;
  focus_type

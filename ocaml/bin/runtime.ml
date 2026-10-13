open Runtime_calculus
module S = Source_calculus

let trace = ref false
let trace_rules = ref false
let max_steps = ref None

(* A driver policy: focus first, then entries in future-name order; choose the
   left operand first when both dereferences apply. The relation keeps all choices. *)
let rec evaluate step remaining state =
  if Runtime_state.final state then state
  else if remaining = Some 0 then
    Zoo.error ~kind:"Step limit" "Stopped at:@.%a" Runtime_print.state state
  else
    match
      Runtime_reduction.steps
        ~fresh:(Runtime_state.fresh state.Runtime_state.signature)
        state
    with
    | (rule, next) :: _ ->
        if !trace then
          Zoo.print_info "  -- %a -->@.%a@." Runtime_print.rule rule
            Runtime_print.state next
        else if !trace_rules then
          Zoo.print_info "  %d: %a@." step Runtime_print.rule rule;
        evaluate (step + 1) (Option.map pred remaining) next
    | [] ->
        Zoo.error ~kind:"Evaluation error"
          "No reduction rule applies to this non-final state:@.%a"
          Runtime_print.state state

module Runtime = Zoo.Main (struct
  let name = "runtime"

  type command = Source_frontend.Frontend.command
  type environment = unit

  let initial_environment = ()

  let options =
    [
      ("--trace", Arg.Set trace, " Display every runtime reduction and state");
      ( "--trace-rules",
        Arg.Set trace_rules,
        " Display numbered runtime rules without states" );
      ( "--max-steps",
        Arg.Int (fun n ->
            if n < 0 then raise (Arg.Bad "--max-steps must be non-negative");
            max_steps := Some n),
        "<n> Stop after at most n runtime steps per input term" );
    ]

  let file_parser = Some (fun () lexbuf -> Source_frontend.Frontend.file lexbuf)

  let toplevel_parser =
    Some (fun () lexbuf -> Source_frontend.Frontend.toplevel lexbuf)

  let exec () = function
    | Error (loc, message) -> Zoo.error ~kind:"Syntax error" ~loc "%s" message
    | Ok command ->
        let source = command.Zoo.data in
        let ty =
          try S.Typing.type_term S.Syntax.Var.Map.empty source
          with S.Typing.Type_error error ->
            Zoo.error ~kind:"Type error" ~loc:command.Zoo.loc "%a" S.Print.error
              error
        in
        let empty = Runtime_syntax.FName.Map.empty in
        let initial = Runtime_state.make empty (Runtime_input.term source) empty in
        if !trace then Zoo.print_info "%a@." Runtime_print.state initial;
        let final = evaluate 1 !max_steps initial in
        match Runtime_observation.observe final with
        | Some value -> Zoo.print_info "- : %a = %a@." S.Print.ty ty S.Print.value value
        | None ->
            Zoo.print_info "Final state : %a@.%a@.No source-value observation.@."
              S.Print.ty ty Runtime_print.state final
end)

let () = Runtime.main ()

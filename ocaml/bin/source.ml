open Source_calculus

let trace = ref false

let rec evaluate term =
  match Reduction.step term with
  | Some (rule, next) ->
      if !trace then
        Zoo.print_info "  -- %a -->@.%a@." Print.rule rule Print.term next;
      evaluate next
  | None -> (
      match term with
      | Syntax.Atom (Syntax.Value value) -> value
      | _ ->
          Zoo.error ~kind:"Evaluation error" "No reduction rule applies to %a"
            Print.term term)

module Source = Zoo.Main (struct
  let name = "source"

  type command = Source_frontend.Frontend.command
  type environment = unit

  let initial_environment = ()

  let options =
    [ ("--trace", Arg.Set trace, " Display every sequential reduction") ]

  let file_parser = Some (fun () lexbuf -> Source_frontend.Frontend.file lexbuf)

  let toplevel_parser =
    Some (fun () lexbuf -> Source_frontend.Frontend.toplevel lexbuf)

  let exec () = function
    | Error (loc, message) -> Zoo.error ~kind:"Syntax error" ~loc "%s" message
    | Ok command ->
        let term = command.Zoo.data in
        let ty =
          try Typing.type_term Syntax.Var.Map.empty term
          with Typing.Type_error error ->
            Zoo.error ~kind:"Type error" ~loc:command.Zoo.loc "%a" Print.error
              error
        in
        if !trace then Zoo.print_info "%a@." Print.term term;
        let value = evaluate term in
        Zoo.print_info "- : %a = %a@." Print.ty ty Print.value value
end)

let () = Source.main ()

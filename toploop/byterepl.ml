open Batteries;;

let run_toploop () =

  Toploop.initialize_toplevel_env () ;
  let _ = Topdirs.dir_untrace_all Format.std_formatter () in

  let null_formatter =
    Format.formatter_of_out_channel IO.stdnull
  in

  let _ = Hashtbl.replace Toploop.directive_table "use"
    (Toploop.Directive_string (Topdirs.dir_use null_formatter))
  in

  let _ = Hashtbl.add Toploop.directive_table "load"
    (Toploop.Directive_string (Topdirs.dir_load null_formatter))
  in

  let topdo s = 
    s
    |> Lexing.from_string
    |> !Toploop.parse_toplevel_phrase
    |> Toploop.execute_phrase false null_formatter
    |> ignore
  in

  topdo "Sys.interactive := false;;" ;
  ignore(Toploop.use_silently null_formatter ".init.ml") ;
  topdo "Sys.interactive := true;;" ;
  topdo "Repl.main ();;"

;;

run_toploop ();;


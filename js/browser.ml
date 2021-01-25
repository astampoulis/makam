open PegRuntime;;
open Batteries;;
open Termlangbuiltin;;
open Termlangcanon;;
open Termlangprolog;;
open Termlangext;;
open Termlangrefl;;
open Termlangparse;;
open Js_of_ocaml;;

let version = Version.version;;

let makam_parser = MakamGrammar.parse_prologcmd ;;
let print_now s = Printf.printf "%s%!" s ;;

let meta_print_exception : (exn -> unit) ref =
  ref (fun e -> print_now "Uncaught OCaml-level exception; use bytecode Makam toplevel to debug.\n")
;;

let jseval s =
  Js.to_string (Js.Unsafe.eval_string s)
;;

builtin_enter_module "js" ;;

  new_builtin_predicate "eval" ( _tString **> _tString **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ script ; output ] -> begin perform
         script <-- chasePattcanon [] script ;
         script <-- _PtoString script ;
         pattcanonUnifyFull output (_PofString (jseval script) ~loc:output.loc)
    end | _ -> assert false)
  ;;

builtin_leave_module () ;;

exception ParsingError;;

let _ =
  let prevparser = !MakamGrammar.makam_toplevel_parser in
  MakamGrammar.makam_toplevel_parser :=
    (fun syntax memo mode input ->
      let res = prevparser syntax memo mode input in
      match res, UChannel.reached_eof input with
	Some(_, uc), false ->
	  print_now ("\nParsing error at " ^ (UChannel.string_of_loc (UChannel.loc uc)) ^ ".\n");
	  raise ParsingError
      | _ -> res)
;;

let (process_input : string -> unit) input =

  let old_debug = ref !Termlangcanon._DEBUG in
  let restore_debug () = Termlangcanon._DEBUG := !old_debug in

  let rec loop input : unit = 

    let recover () =
      let furthest = UChannel.flush_to_furthest input in
      let rec find_newline input =
	match UChannel.get_one input with
	    Some(c, input') when (try UChar.char_of c = '\n' with _ -> false) -> loop input'
	  | Some(_, input') -> find_newline input'
	  | None -> ()
      in
      find_newline furthest
    in
    let last_cmd_span () = UChannel.string_of_span !MakamGrammar.last_command_span in

    try
    begin
      old_debug := !Termlangcanon._DEBUG ;

      let res = Peg.parse_of_uchannel makam_parser input in

      let _ = IO.flush stdout in

      if not (UChannel.at_eof input) then
      match res with
          Some(_, input') -> loop input'
	| _ -> print_now
	           ("\nParsing error at " ^
		    (input |> UChannel.loc |> UChannel.string_of_loc) ^
		    ".\n");
	       recover ()
    end 
      with 
      | BatInnerIO.Input_closed -> ()
      | Termlangcanon.FileNotFound(s, all) ->
	(Printf.printf "In %s:\n  File %s not found (searched: %a).\n%!"
	               (last_cmd_span ()) s
                       (List.print ~first:"[" ~last:"]" ~sep:"; " String.print) all
        ; loop (UChannel.flush_to_furthest input))
      | Termlangcanon.TypingError | Termlangprolog.PrologError | ParsingError ->
        (restore_debug (); loop (UChannel.flush_to_furthest input))
      | Termlangrefl.StagingError(code) ->
        (Printf.printf "In %s:\n  Error in staged code.\n%!"
                    (UChannel.string_of_span code.loc)
        ; restore_debug (); loop (UChannel.flush_to_furthest input))
      | Termlangprolog.ResetInModule m ->
	(Printf.printf "In %s:\n  Module %s tried to reset the state.\n%!"
	   (last_cmd_span ()) m; loop (UChannel.flush_to_furthest input))
      | Termlangcanon.NotInModule ->
	(Printf.printf "In %s:\n  Stopping extension to module, but no module is open.\n%!"
	   (last_cmd_span ()); loop (UChannel.flush_to_furthest input))
      | MakamGrammar.NoTestSuite ->
         (Printf.printf "In %s:\n  Test suite has not been specified, use %%testsuite directive.\n%!"
            (last_cmd_span ()); loop (UChannel.flush_to_furthest input))
      | MakamGrammar.NoQueryToTest ->
         (Printf.printf "In %s:\n  Last command was not a query.\n%!"
            (last_cmd_span ()); loop (UChannel.flush_to_furthest input))
      | Peg.IncompleteParse(_, s) ->
        (print_now ("\nParse error at " ^ (UChannel.string_of_loc s) ^ ".\n"); restore_debug (); loop (UChannel.flush_to_furthest input))
      | e ->
	raise e
  in
  loop (UChannel.from_string input)
;;

let load_init_files () =
  let loadfile s =
    global_load_file_resolved (fun syntax -> Peg.parse_of_file (!MakamGrammar.makam_toplevel_parser syntax)) s
  in
  loadfile (global_resolve_filename "stdlib/init.makam") ;
  if Sys.file_exists "init.makam" then loadfile "init.makam" ;
  Termlangcanon.builtinstate := !globalstate ;
  Termlangprolog.builtinprologstate := !globalprologstate
;;    


let main () =

  Termlangcanon.global_term_reset ();
  Termlangprolog.global_reset ();
  global_set_cache_directory None;
  load_init_files ()

;;


let js_process_input_batch s =
  let output = ref "" in
  Sys_js.set_channel_flusher Stdlib.stdout (fun s -> output := (!output) ^ s) ;
  Sys_js.set_channel_flusher Stdlib.stderr (fun s -> output := (!output) ^ s) ;
  process_input (Js.to_string s);
  Js.string !output
;;

let js_process_input_interactive s =
  process_input (Js.to_string s)
;;

let define_as_worker () =
  Sys_js.set_channel_flusher Stdlib.stdout (fun s ->
    Js.Unsafe.meth_call (Js.Unsafe.variable "self") "postMessage"
    [| Js.Unsafe.inject (Js.string s) |]);
  Js.Unsafe.meth_call (Js.Unsafe.variable "self") "addEventListener"
    [| Js.Unsafe.inject (Js.string "message");
       Js.Unsafe.inject (Js.wrap_callback (fun e ->
	 process_input (Js.to_string (Js.Unsafe.get e "data"))));
       Js.Unsafe.inject Js._false |]

let define_as_global () =
  Js.Unsafe.set Js.Unsafe.global "makam" 
    (Js.wrap_callback js_process_input_batch)
;;

let define_as_export () =
  Js.Unsafe.set (Js.Unsafe.variable "module") "exports" 
    (Js.Unsafe.obj [| ("eval", Js.Unsafe.inject (Js.wrap_callback js_process_input_interactive));
                      ("version", Js.Unsafe.inject (Js.string version)) |])
;;

let _ = 

  main();
  if Js.Unsafe.eval_string "typeof module !== 'undefined'" then
    define_as_export ()
  else if Js.Unsafe.eval_string "typeof WorkerGlobalScope !== 'undefined' && self instanceof WorkerGlobalScope" then
    define_as_worker ()
  else
    define_as_global ()

;;
    

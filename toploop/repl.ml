open PegRuntime;;
open Batteries;;
open Termlangbuiltin;;
open Termlangcanon;;
open Termlangprolog;;
open Termlangext;;
open Termlangrefl;;
open Termlangparse;;

let version = Version.version;;

let makam_parser = MakamGrammar.parse_prologcmd ;;
let print_now s = Printf.printf "%s%!" s ;;

let meta_print_exception : (exn -> unit) ref =
  ref (fun e -> print_now "Uncaught OCaml-level exception; use bytecode Makam toplevel to debug.\n")
;;

let _ =
  Benchmark.precise_clock := (fun () -> (Mtime.Span.to_ns (Mtime_clock.elapsed ()) *. 1e-9) -. !Benchmark.pausedtimeelapsed)
;;

(* JavaScript support. Requires node; sessions are not persistent. *)

let jseval s =
  let (inp, outp) = Unix.open_process "node" in
  (* TODO: I am sure there is a less gross way to do this... *)
  BatInnerIO.nwrite outp ("const result = " ^ s ^ "; console.log('>>>>>' + result + '<<<<<');");
  BatInnerIO.close_out outp;
  let res = BatInnerIO.read_all inp in
  BatInnerIO.close_in inp;
  try
    let (_, suffix) = String.split res ">>>>>" in
    let (result, _) = String.split suffix "<<<<<" in
    Some(result)
  with Not_found -> None
;;

builtin_enter_module "js" ;;

  new_builtin_predicate "eval" ( _tString **> _tString **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ script ; output ] -> begin perform
         script <-- chasePattcanon [] script ;
         script <-- _PtoString script ;
         match jseval script with
           Some res -> pattcanonUnifyFull output (_PofString res ~loc:output.loc)
         | None -> mzero
    end | _ -> assert false)
  ;;

builtin_leave_module () ;;

(* Backtracking for ProofGeneral *)

let get_full_state () =
  let doit _ x = !x in
  let (a0, a1,
       a2, a3, a4, a5,
       a6, a7, a8, a9, a10) = "", "", "", "", "", "", "", "", "", "", "" in
  (doit a0 globalstate, doit a1 globalprologstate,
   doit a2 _DEBUG, doit a3 _DEBUG_DEMAND, doit a4 _DEBUG_NAMES, doit a5 _DEBUG_TYPES,
   doit a6 _DEBUG_STAGING, doit a7 _BENCHMARK, doit a8 _LOGGING, doit a9 _ONLY_TYPECHECK,
   doit a10 last_query_successful)
;;

let set_full_state st =
  let doit a x = x := a in
  let (a0, a1,
       a2, a3, a4, a5,
       a6, a7, a8, a9, a10) = st in
  ignore
  (doit a0 globalstate, doit a1 globalprologstate,
   doit a2 _DEBUG, doit a3 _DEBUG_DEMAND, doit a4 _DEBUG_NAMES, doit a5 _DEBUG_TYPES,
   doit a6 _DEBUG_STAGING, doit a7 _BENCHMARK, doit a8 _LOGGING, doit a9 _ONLY_TYPECHECK,
   doit a10 last_query_successful)
;;

let next_state_name =
  let i = ref 0 in
  fun () ->
    i := !i + 1;
    "command-" ^ (string_of_int !i)
;;

let statedict =
  let dict  = Dict.empty in
  let dict = Dict.add "" (get_full_state ()) dict in
  ref dict
;;

let store_state () =
  let name = next_state_name () in
  statedict := Dict.add name (get_full_state ()) !statedict
;;

let forget_to_state s =
  let state' = Dict.find s !statedict in
  set_full_state state'
;;

(* The repl. *)


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

let use_files files =
  String.concat "\n" (List.map (fun s -> "%use \"" ^ s ^ "\".") files)
;;

let rec repl ?input () : unit =
  Sys.catch_break true;
  let input, prompt, reached_eof, is_stdin =
    match input with
    | Some input ->
       let initloc =
         let open UChannel in
         { description = "<command-line>" ; lineno = 1; charno = 1; offset = 0 }
       in
       UChannel.from_string ~initloc:initloc input, "", UChannel.at_eof, false
    | None ->
      UChannel.from_stdin (), "# ", UChannel.reached_eof, true
  in
  let old_debug = ref false in
  let restore_debug () = Termlangcanon._DEBUG := !old_debug in
  let last_cmd_span () = UChannel.string_of_span !MakamGrammar.last_command_span in
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
    if not (reached_eof input) then
    print_now prompt;

    try
    begin
      old_debug := !Termlangcanon._DEBUG ;

      let res = Peg.parse_of_uchannel makam_parser input in

      let _ = IO.flush stdout in

      if not (reached_eof input) then
      match res with
          Some(_, input') -> store_state (); loop input'
        | _ ->
           if is_stdin then
             raise (Peg.IncompleteParse(input, input |> UChannel.loc |> UChannel.string_of_loc))
           else
             recover ()
    end
      with
      | BatInnerIO.Input_closed -> ()
      | Sys.Break ->
        (print_now "\nInterrupted.\n"; restore_debug () ; if is_stdin then repl () else loop (UChannel.flush_to_furthest input))
      | Termlangcanon.FileNotFound(s, all) ->
        (Printf.printf "In %s:\n  File %s not found (searched: %a).\n%!"
                       (last_cmd_span ()) s
                       (List.print ~first:"[" ~last:"]" ~sep:"; " String.print) all
        ; loop (UChannel.flush_to_furthest input))
      | Termlangcanon.TypingError | Termlangprolog.PrologError | ParsingError ->
        (restore_debug (); loop (UChannel.flush_to_furthest input))
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
      | MakamGrammar.Forget(s) ->
        (forget_to_state s; loop (UChannel.flush_to_furthest input))
      | Peg.IncompleteParse(_, s) ->
        (print_now ("\nParse error at " ^ s ^ ".\n"); restore_debug (); loop (UChannel.flush_to_furthest input))
      | e ->
        raise e
        (*
        !meta_print_exception e ;
        flush IO.stdout;
        restore_debug () ;
        loop (UChannel.flush_to_furthest input)
        *)
  in
  loop input


let benchmark_results () =
  let results = Benchmark.cumulative_results () in
  if not (List.is_empty results) then
    print_now
      (Printf.sprintf "Benchmark results:\n\n%a\n%!" (List.print ~first:"" ~sep:"\n" ~last:""
                            (Utils.Pair.print ~first:"" ~sep:": " ~last:"" String.print Float.print))
        results)
;;

let output_log () =
  if not (List.is_empty !(Benchmark.loglist)) then
    (File.with_file_out "logprofile/log.csv" Benchmark.print_log)
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

open BatOptParse;;
let run_tests = ref false;;

let parse_options () =
  let parsr =
    OptParser.make
      ~version:version
      ~prog:"makam"
      ~description:
      (String.concat
         ""
         [ "Makam, version "; version; " -- "; "A tool for rapid language prototyping" ])
      ()
  in
  let includes = StdOpt.str_callback ~metavar:"directory" global_add_directory in
  let _ = OptParser.add parsr ~short_name:'I' ~long_name:"include"
                        ~help:"include the directory in the search path for makam files"
                        includes
  in
  let runTests = StdOpt.store_true () in
  let _ = OptParser.add parsr ~short_names:[] ~long_name:"run-tests"
                        ~help:"run tests after loading files"
                        runTests
  in
  let files = OptParser.parse_argv parsr in
  run_tests := Opt.get runTests;
  files
;;

let main () =
  let files = parse_options () in
  print_now ("\n\tMakam, version " ^ version ^ "\n\n");
  load_init_files ();
  store_state ();
  let doexit, files =
    match List.rev files with
      [] -> false, files
    | stdin :: tl when stdin = "-" ->
       false, List.rev tl
    | _ -> true, files
  in
  repl ~input:(use_files files) ();
  if !run_tests then repl ~input:"run_tests X ?\n" ();

  if not doexit then repl ();
  print_now "\n";
  benchmark_results ();
  output_log ();
  match !last_query_successful with
  | None | Some true -> ()
  | Some false -> exit 1
;;

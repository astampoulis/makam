open PegRuntime;;
open Batteries;;
open Termlangbuiltin;;
open Termlangcanon;;
open Termlangprolog;;
open Termlangext;;
open Termlangrefl;;
open Termlangparse;;

let version = Version.version;;

let default_makam_cache_dir = ".makam-cache";;
let makam_parser = MakamGrammar.parse_prologcmd ;;
let print_now s = Printf.printf "%s%!" s ;;

let _ =
  (* Seed the input statehash with the hash of makam's source code.
     This way cached predicates get invalidated when there are changes
     to the implementation. *)
  UChannel.input_statehash := Hashtbl.hash Version.source_hash
;;

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
       a6, a7, a8, a9, a10, a11) = "", "", "", "", "", "", "", "", "", "", "", "" in
  (doit a0 globalstate, doit a1 globalprologstate,
   doit a2 _DEBUG, doit a3 _DEBUG_DEMAND, doit a4 _DEBUG_NAMES, doit a5 _DEBUG_TYPES,
   doit a6 _DEBUG_STAGING, doit a7 _BENCHMARK, doit a8 _LOGGING, doit a9 _ONLY_TYPECHECK,
   doit a10 last_query_successful, doit a11 UChannel.input_statehash)
;;

let set_full_state st =
  let doit a x = x := a in
  let (a0, a1,
       a2, a3, a4, a5,
       a6, a7, a8, a9, a10, a11) = st in
  ignore
  (doit a0 globalstate, doit a1 globalprologstate,
   doit a2 _DEBUG, doit a3 _DEBUG_DEMAND, doit a4 _DEBUG_NAMES, doit a5 _DEBUG_TYPES,
   doit a6 _DEBUG_STAGING, doit a7 _BENCHMARK, doit a8 _LOGGING, doit a9 _ONLY_TYPECHECK,
   doit a10 last_query_successful, doit a11 UChannel.input_statehash)
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

let persist_state filename =
  let state = get_full_state() in
  let content = Marshal.to_string state [Marshal.Closures] in
  try
    let output = File.open_out filename in
    let _ = IO.nwrite output content in
    let _ = IO.close_out output in
    ()
  with _ -> ()
;;

let restore_state filename =
  let input = File.open_in filename in
  let state = Marshal.from_string (IO.read_all input) 0 in
  let _ = IO.close_in input in
  set_full_state state
;;


(* The repl. *)


exception ErrorInFile;;

let exception_handler (type a) (f: unit -> a) (recover: unit -> a) (recover_parse: unit -> a) =
  let last_cmd_span () = !MakamGrammar.last_command_span in
  try f ()
  with
  | Termlangcanon.FileNotFound(s, all) ->
     (Log.error (last_cmd_span ())
     (Printf.sprintf "File %s not found (searched: %a)."
                    s (List.print ~first:"[" ~last:"]" ~sep:"; " String.print) all)
     ; recover())
  | Termlangcanon.TypingError | Termlangprolog.PrologError ->
     (recover())
  | Termlangrefl.StagingError(code) ->
     (Log.error code.loc
     "Error in staged code."
     ; recover())
  | Termlangprolog.ResetInModule m ->
     (Log.error (last_cmd_span ())
     (Printf.sprintf "Module %s tried to reset the state." m)
     ; recover())
  | Termlangcanon.NotInModule ->
     (Log.error (last_cmd_span ())
     "Stopping extension to module, but no module is open."
     ; recover())
  | MakamGrammar.NoTestSuite ->
     (Log.error (last_cmd_span ())
     "Test suite has not been specified, use %testsuite directive."
     ; recover())
  | MakamGrammar.NoQueryToTest ->
     (Log.error (last_cmd_span ())
     "Last command was not a query."
     ; recover())
  | MakamGrammar.Forget(s) ->
     (forget_to_state s; recover())
  | Peg.IncompleteParse(_, s) ->
     (Log.error (UChannel.mk_span s s)
     "Parse error."
     ; recover_parse())
  | ErrorInFile -> recover ()
(*
  | e ->
     raise e
     !meta_print_exception e ;
     flush IO.stdout;
     restore_debug () ;
     loop (UChannel.flush_to_furthest input)
*)
;;

let _ =
  let prevparser = !MakamGrammar.makam_toplevel_parser in
  MakamGrammar.makam_toplevel_parser :=
    (fun syntax memo mode input ->
      let restore_interactivity = let value = !is_interactive in fun () -> is_interactive := value in
      let _ = is_interactive := false in
      exception_handler (fun _ ->
        let res = prevparser syntax memo mode input in
        match res, UChannel.reached_eof input with
          Some(_, uc), false ->
            raise (Peg.IncompleteParse(uc, UChannel.loc uc))
        | _ -> restore_interactivity (); res)
        (fun _ -> restore_interactivity (); raise ErrorInFile)
        (fun _ -> restore_interactivity (); raise ErrorInFile))
;;


let rec repl ?input () : unit =
  Sys.catch_break true;
  let input, reached_eof, is_stdin =
    match input with
    | Some input ->
       let initloc =
         let open UChannel in
         { description = "<command-line>" ; lineno = 1; charno = 1; offset = 0 }
       in
       UChannel.from_string ~initloc:initloc input, UChannel.at_eof, false
    | None ->
      UChannel.from_stdin (), UChannel.reached_eof, true
  in
  let _ =
    is_interactive := is_stdin && Unix.isatty Unix.stdin
  in
  let prompt =
    if !is_interactive then "# " else if is_stdin then "## Ready for input.\n" else ""
  in
  let old_debug = ref false in
  let restore_debug () = Termlangcanon._DEBUG := !old_debug in
  let rec loop input : unit =

    let recover () =
      loop (UChannel.flush_to_furthest input)
    in
    let skip_line_and_recover () =
      let furthest = UChannel.flush_to_furthest input in
      let rec find_newline input =
        match UChannel.get_one input with
            Some(c, input') when (try UChar.char_of c = '\n' with _ -> false) -> loop input'
          | Some(_, input') -> find_newline input'
          | None -> ()
      in
      find_newline furthest
    in

    if not (reached_eof input) then begin
    print_now prompt;

    (try
      exception_handler (fun () ->
      begin
        old_debug := !Termlangcanon._DEBUG ;

        let res = Peg.parse_of_uchannel makam_parser input in

        let _ = IO.flush stdout in

        if not (reached_eof input) then
        match res with
          | Some(_, input') ->
             store_state (); loop input'
          | None ->
             raise (Peg.IncompleteParse(input, input |> UChannel.loc))
      end)
      (fun () -> restore_debug (); if !is_interactive then recover () else (raise ErrorInFile))
      (fun () -> restore_debug (); if !is_interactive then skip_line_and_recover () else (raise ErrorInFile))
     with
     | BatInnerIO.Input_closed -> ()
     | Sys.Break ->
       (print_now "\nInterrupted.\n";
        restore_debug (); if !is_interactive then repl ()))
    end
  in
  loop input
;;

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

let load_file_resolved s =
  global_load_file_resolved (fun syntax -> Peg.parse_of_file (!MakamGrammar.makam_toplevel_parser syntax)) s
;;

let load_file s =
  global_load_file (fun syntax -> Peg.parse_of_file (!MakamGrammar.makam_toplevel_parser syntax)) s
;;

let load_init_files () =
  load_file "stdlib/init.makam" ;
  if Sys.file_exists "init.makam" then load_file_resolved "init.makam" ;
  Termlangcanon.builtinstate := !globalstate ;
  Termlangprolog.builtinprologstate := !globalprologstate
;;

open BatOptParse;;
let run_tests = ref false;;
let init_state = ref None;;
let persist_state_to = ref None;;

let parse_options () =
  let parsr =
    OptParser.make
      ~version:(version ^ " source-hash:" ^ Version.source_hash)
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
  let defaultCacheDir = StdOpt.store_const ~default:(Some default_makam_cache_dir) None in
  let cacheSet =
    StdOpt.str_callback ~metavar:"cachedir" (fun s -> Opt.set defaultCacheDir (Some s))
  in
  let _ = OptParser.add parsr ~short_name:'C' ~long_name:"cache-dir"
                              ~help:("set the directory where cache files are written (default: ./" ^ default_makam_cache_dir ^ ")")
                              cacheSet
  in
  let _ = OptParser.add parsr ~long_name:"no-cache"
                              ~help:"disable result cache"
                              defaultCacheDir
  in
  let initState =
    StdOpt.str_callback ~metavar:"statefile" (fun s -> init_state := Some s)
  in
  let _ = OptParser.add parsr ~long_name:"init-state"
                              ~help:"load initial state from file"
                              initState
  in
  let persistStateTo =
    StdOpt.str_callback ~metavar:"statefile" (fun s -> persist_state_to := Some s)
  in
  let _ = OptParser.add parsr ~long_name:"persist-state"
                              ~help:"persist state to file upon exit"
                              persistStateTo
  in

  let files = OptParser.parse_argv parsr in
  run_tests := Opt.get runTests;
  global_set_cache_directory (Opt.get defaultCacheDir);

  files
;;

let main () =

  let files = parse_options () in
  let doexit, files =
    match List.rev files with
      [] -> false, files
    | stdin :: tl when stdin = "-" ->
       false, List.rev tl
    | _ -> true, files
  in

  print_now ("\n\tMakam, version " ^ version ^ "\n\n");

  let toplevel_error_happened = ref false in
  let handle_error () = toplevel_error_happened := true in

  exception_handler begin fun _ ->
    if Option.is_some !init_state then restore_state (Option.get !init_state) else load_init_files ();
    store_state ();
    List.iter load_file files ;
    if !run_tests then repl ~input:"run_tests X ?" ();
    if not doexit then repl ()
  end handle_error handle_error;

  benchmark_results ();
  output_log ();
  if Option.is_some !persist_state_to then persist_state (Option.get !persist_state_to);
  match !toplevel_error_happened, !last_query_successful with
  | false, None | false, Some true -> ()
  | false, Some false | true, _ -> exit 1
;;

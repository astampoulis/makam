(* Functions to stage ASTs to the toploop *)
open ToploopTools;;
open Peg;; 
open PegRuntime;;
open Batteries;;
open Termlangcanon;;
(*
open Termlangprolog;;
open Termlangext;;
*)

let toploopGrammar =
  let open BatMap in
  let openmodules : float Dict.t ref = ref (Dict.empty) in
  function s ->
    let filename = "grammars/mod" ^ s ^ ".peg" in
    let newtime = let open Unix in (stat filename).st_mtime in
    try
      let time = Dict.find s !openmodules in
      if newtime > time then
	(openmodules := Dict.empty; raise Not_found)
      else
	()
    with Not_found ->
      let _ = Peg.parse_of_file PegGrammar.parse_peg filename |> parseGen |> useModuleAST s "generated/temp.ml" in
      openmodules := Dict.add s newtime !openmodules;
      Printf.printf "Loaded external grammar %s.\n" s
;;


(*
let exprParser t p =
  Termlangcanon.add_expr_parser (!@ t)
  (fun t s loc -> Peg.parse_of_string p ~initloc:loc s)
;;
*)

let eval ?(silent = true) s =
  s
    |> Lexing.from_string
    |> !Toploop.parse_toplevel_phrase
    |> Toploop.execute_phrase (not silent) Format.std_formatter
    |> ignore
;;

let toploopExprParser (t : string) (s : string) =
  eval (Printf.sprintf "exprParser %a %s;;" String.print_quoted t s)
;;


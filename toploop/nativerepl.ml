open PegRuntime;;
open Batteries;;
open Termlangcanon;;
open Termlangprolog;;
open Termlangext;;
open Termlangrefl;;

open Ast_helper;;

let read_process command =
  let buffer_size = 2048 in
  let buffer = Buffer.create buffer_size in
  let string = String.create buffer_size in
  let in_channel = Unix.open_process_in (command ^ " 2>&1") in
  let chars_read = ref 1 in
  while !chars_read <> 0 do
    chars_read := input in_channel string 0 buffer_size;
    Buffer.add_substring buffer string 0 !chars_read
  done;
  ignore (Unix.close_process_in in_channel);
  Buffer.contents buffer
;;

let compile filename = 
  let (res, outputname) = String.replace filename ".ml" ".cmxs" in
  let _ = assert res in
  let ret = Sys.command ("ocamlbuild -use-ocamlfind " ^ outputname) in
  if ret = 0 then
    "_build/" ^ outputname
  else
    raise Termlangrefl.CompilationFailure
;;

let writeout s = 
  let filename = Filename.temp_file ~temp_dir:"generated" "in" ".ml" in
  File.with_file_out
    ~mode:[ `create; `trunc ] filename
    (fun file -> IO.nwrite file s);
  filename
;;

meta_do := fun s ->
           
           let file = writeout s in
	   try
             file |> compile |> Dynlink.loadfile ;
             Sys.remove file
	   with Termlangrefl.CompilationFailure ->
	     Sys.remove file ;
	     raise Termlangrefl.CompilationFailure

;;

            

Termlangcanon.global_term_reset ();;
Termlangprolog.global_reset ();;
Repl.main ();;

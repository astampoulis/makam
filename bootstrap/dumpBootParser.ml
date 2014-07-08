open Batteries;;
open Peg;;
open ToploopTools;;

open Camlp4.PreCast;;
let _loc = Loc.ghost;;

open BootPegGrammar;;


let main () =
  if Array.length Sys.argv <> 2 then
    (let usage =
	   "\
            Usage: dumpBootParser [output]\n\
                   [output] is the file where the generated ML code is printed\n"
     in
     print_string usage)
  else
    (let generate_parser output = 
       let ast = parseGen pegGrammar in
       let ast = <:str_item< open Batteries;; open Peg;; $ast$ >> in
       let str = ToploopTools.returnAST ast in
       File.with_file_out output (fun oc -> Printf.fprintf oc "%s" str)
     in
     generate_parser Sys.argv.(1))
;;

main ();;

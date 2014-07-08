open Batteries;;
open Peg;;
open PegBuiltins;;
open ToploopTools;;
open Camlp4.PreCast;;
let _loc = Loc.ghost;;

module Make =

  functor(PegParser : sig
    val parse_peg : pegGrammar parser_t
  end) ->
    struct
      
    let main () =
      if Array.length Sys.argv <> 3 then
	(let usage =
	   "\
            Usage: pegParseGen [file] [output]\n\
                   [file]   is a file containing a PEG grammar\n\
                   [output] is the file where the generated ML code is printed\n"
	 in
         print_string usage)
      else
	(let generate_parser input output = 
	   let g   = parse_of_file PegParser.parse_peg input in
	   let ast = ToploopTools.returnAST (parseGen g) in
	   File.with_file_out output (fun oc -> Printf.fprintf oc "%s" ast)
	 in
	 generate_parser Sys.argv.(1) Sys.argv.(2))


    end ;;

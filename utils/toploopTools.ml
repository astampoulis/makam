let returnAST str_item =
  let module ExportAst = struct
    open Lexing;;
    open Camlp4;;
    open PreCast;;
    open Camlp4.Sig;;
    module Ast2pt = Camlp4.Struct.Camlp4Ast2OCamlAst.Make(Ast);;
    module Lexer = Camlp4.Struct.Lexer.Make(Token);;
    module Printer = Camlp4.Printers.OCaml.Make(Camlp4.PreCast.Syntax);;
    module Dumper = Camlp4.Printers.DumpOCamlAst.Make(Camlp4.PreCast.Syntax);;
    
    let printer = (new Printer.printer ())#implem
    let dumper = Dumper.print_implem
  end
  in
  ExportAst.printer Format.str_formatter str_item;
  Format.flush_str_formatter () ;;

let parseAST s =
  try
    Camlp4.PreCast.Syntax.AntiquotSyntax.parse_expr Camlp4.PreCast.Loc.ghost s
  with _ ->
    (let module ParseAst =
	 struct
	   open Lexing;;
	   open Camlp4;;
	   open PreCast;;
	   open Camlp4.Sig;;
	   module Caml0 = Camlp4OCamlRevisedParser.Make(Syntax);;
	   module Caml = Camlp4OCamlParser.Make(Syntax);;
	   
	   let reader_expr s = Caml.AntiquotSyntax.parse_expr Loc.ghost s ;;
	 end
     in
     try
       ParseAst.reader_expr s
     with _ ->
       failwith ("failed to parse OCaml AST "^s^"\n")
       ) ;;


let parseAST_stritem s =
  try
    Camlp4.PreCast.Syntax.parse_implem Camlp4.PreCast.Loc.ghost (Stream.of_string s)
  with _ -> 
    (let module ParseAst =
	 struct
	   open Lexing;;
	   open Camlp4;;
	   open PreCast;;
	   open Camlp4.Sig;;
	   module Caml0 = Camlp4OCamlRevisedParser.Make(Syntax);;
	   module Caml = Camlp4OCamlParser.Make(Syntax);;
	   
	   let reader_stritem s = 
	     Syntax.parse_implem Loc.ghost (Stream.of_string s) ;;
	   
	 end
     in
     try
       ParseAst.reader_stritem s
     with _ ->
       failwith ("failed to parse OCaml AST "^s^"\n"))
;;



  

let dumpAST str_item =
  let module ExportAst = struct
    open Lexing;;
    open Camlp4;;
    open PreCast;;
    open Camlp4.Sig;;
    module Ast2pt = Camlp4.Struct.Camlp4Ast2OCamlAst.Make(Ast);;
    module Lexer = Camlp4.Struct.Lexer.Make(Token);;
    module Printer = Camlp4.Printers.OCaml.Make(Camlp4.PreCast.Syntax);;
    module Dumper = Camlp4.Printers.DumpOCamlAst.Make(Camlp4.PreCast.Syntax);;
    
    let printer = (new Printer.printer ())#implem
    let dumper = Dumper.print_implem
  end
  in
  ExportAst.dumper str_item ;;

let printAST str_item = print_string (returnAST str_item) ;;

let saveAST filename str_item =
  BatFile.with_file_out ~mode:[`create; `trunc; `text] filename
    (fun oc -> BatIO.nwrite oc (returnAST str_item)) ;;

let defAST str_item =
  let module Staging = struct
    open Lexing;;
    open Camlp4;;
    open PreCast;;
    open Camlp4.Sig;;
    module Ast2pt = Camlp4.Struct.Camlp4Ast2OCamlAst.Make(Ast);;
    module Lexer = Camlp4.Struct.Lexer.Make(Token);;
    module Printer = Camlp4.Printers.OCaml.Make(Camlp4.PreCast.Syntax);;
    
    let printer = (new Printer.printer ())#implem
          
    let stage str_item =
      ignore(Toploop.execute_phrase true Format.std_formatter (Obj.magic (Ast2pt.phrase str_item)))
  end
  in
  Staging.stage str_item ;;

(* this is better than defAST because it reports type errors *)
let useAST filename str_item =
  saveAST filename str_item ;
  let ( |> ) arg f = f arg in
  "#use \"" ^ filename ^ "\" ;;\n"
    |> Lexing.from_string
    |> !Toploop.parse_toplevel_phrase
    |> Toploop.execute_phrase false Format.std_formatter ;;

let useModuleAST modulename filename str_item =
  let str_item = 
    let open Camlp4 in
    let open PreCast in
    let _loc = Loc.ghost in
    <:str_item< module $uid:modulename$ = struct $str_item$ end ;; >>
  in
  saveAST filename str_item ;
  let ( |> ) arg f = f arg in
  "#use \"" ^ filename ^ "\" ;;\n"
    |> Lexing.from_string
    |> !Toploop.parse_toplevel_phrase
    |> Toploop.execute_phrase false Format.std_formatter ;;


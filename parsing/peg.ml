(* PEG Parser Generator for OCaml
   ------------------------------
   Written by Antonis Stampoulis; licensed under GPLv3.

   - Supports Unicode files. 
   - Explicit memoization operation (memoize after each non-terminal
      to get packrat parser).
   - Parametric parsers are supported nicely -- they generate parametric
     OCaml functions. Might be useful for modularity/extensibility.
     (Most of the complexity in the code comes from this)
   - Left-recursion is supported, yet not with the semantics I would 
     like -- this is still a matter of investigation.
   - Unsafe casts are used to store things in the memotable; this
     is done so that a sparse memotable can be maintained.
   - Dependent parsing is allowed (through empty parameters used
     for their semantic actions), but does not work correctly
     in the presence of memoization.

*)

open Batteries;;
open UChar;;
open Utils;;
open PegRuntime;;

type ustring = UString.t;;
(* Identifiers and maps of identifiers *)

xtype ident =
    `Id      id : ustring ;;

module IdentOrdered =
  struct
    type t = ident ;;
    let compare (`Id id1) (`Id id2)= UString.compare id1#id id2#id ;;
  end ;;

module IdentMap = Map.Make(IdentOrdered) ;;
type 'a identMap = 'a IdentMap.t ;;
module IdentSet = Set.Make(IdentOrdered) ;;


let needed_memocells_external : (int IdentMap.t) ref = ref IdentMap.empty ;;

(* PEG grammars *)

xtype parsePrim = 
      `AnyChar
    | `CharClass    chars : ustring
    | `Test         p : parsePrim ; test : Camlp4.PreCast.Ast.expr
    | `String       s : ustring
    | `Neg          p : parsePrim
    | `Lookahead    p : parsePrim
    | `Option       p : parsePrim
    | `Choice       p1 : parsePrim ; p2 : parsePrim
    | `Concat       p : parsePrim list ; names : string option list ; action : Camlp4.PreCast.Ast.expr
    | `Nonterm      nonterm : ident ; params : parsePrim list
    | `External     nonterm : ident ; params : parsePrim list
    | `Empty
    | `Void
    | `Memo         p : parsePrim
    | `Param        i : int ; name : ident ;;

xtype nonterminalDef =
    `NonTermDef   params : ident list ; prod : parsePrim ;;

xtype pegGrammar =
    `Peg          entries : nonterminalDef identMap ; exports : string identMap ; preamble : Camlp4.PreCast.Ast.str_item option ; postamble : Camlp4.PreCast.Ast.str_item option ;;


(* Very-very ugly boilerplate code for parsePrim follows.
   In the future, syntax_xtype should generate these for each xtype. *)

module ParsePrim =
  struct

    (* Mendler-style fold *)
    xtype 'r fold_args = `MK
      fAnyChar : { 'pr -> 'pr } ;
      fCharClass : {'pr -> chars:ustring -> 'pr } ;
      fTest : {'pr -> recc:('pr -> parsePrim -> 'pr) -> p:parsePrim -> test:Camlp4.PreCast.Ast.expr -> 'pr } ;
      fString : {'pr -> s:ustring -> 'pr } ;
      fNeg : {'pr -> recc:('pr -> parsePrim -> 'pr) -> p:parsePrim -> 'pr } ;
      fLookahead : {'pr -> recc:('pr -> parsePrim -> 'pr) -> p:parsePrim -> 'pr } ;
      fOption : {'pr -> recc:('pr -> parsePrim -> 'pr) -> p:parsePrim -> 'pr } ;
      fChoice : {'pr -> recc:('pr -> parsePrim -> 'pr) -> p1:parsePrim -> p2:parsePrim -> 'pr } ;
      fConcat : {'pr -> recc:('pr -> parsePrim -> 'pr) -> p:(parsePrim list) -> names:(string option list) -> action:Camlp4.PreCast.Ast.expr -> 'pr } ;
      fNonterm : {'pr -> recc:('pr -> parsePrim -> 'pr) -> nonterm:ident -> params:(parsePrim list) -> 'pr } ;
      fExternal  : {'pr -> recc:('pr -> parsePrim -> 'pr) -> nonterm:ident -> params:(parsePrim list) -> 'pr } ;
      fEmpty : {'pr -> 'pr } ;
      fVoid : { 'pr -> 'pr } ;
      fMemo : {'pr -> recc:('pr -> parsePrim -> 'pr) -> p:parsePrim -> 'pr } ;
      fParam : { 'pr -> i:int -> name:ident -> 'pr }
    ;;


    let fold_default =
      let (`MK fd) : 'a fold_args =
	<{ fold_args.MK
	     fAnyChar   = ( fun r -> r );
  	     fCharClass = ( fun r ~chars -> r ) ;
	     fTest      = ( fun r ~recc ~p ~test -> recc r p ) ;
	     fString    = ( fun r ~s -> r ) ;
	     fNeg       = ( fun r ~recc ~p -> recc r p ) ;
	     fLookahead = ( fun r ~recc ~p -> recc r p ) ;
	     fOption    = ( fun r ~recc ~p -> recc r p ) ;
	     fChoice    = ( fun r ~recc ~p1 ~p2 -> recc (recc r p1) p2 ) ;
	     fConcat    = ( fun r ~recc ~p ~names ~action -> List.fold_left recc r p ) ;
	     fNonterm   = ( fun r ~recc ~nonterm ~params -> List.fold_left recc r params ) ;
	     fExternal  = ( fun r ~recc ~nonterm ~params -> List.fold_left recc r params ) ;
	     fEmpty     = ( fun r -> r ) ;
	     fVoid      = ( fun r -> r ) ;
	     fMemo      = ( fun r ~recc ~p -> recc r p) ;
	     fParam     = ( fun r ~i ~name -> r )
	 }>
      in fd
    ;;
      
    let fold (args : 'a fold_args) (init : 'a) (cur : parsePrim) =
      let (`MK args) = args in
      let rec aux init cur =
	match cur with
	  `AnyChar _ -> args#fAnyChar init
	| `CharClass o -> args#fCharClass init ~chars:o#chars
	| `Test o -> args#fTest init ~recc:aux ~p:o#p ~test:o#test
	| `String o -> args#fString init ~s:o#s
	| `Neg o -> args#fNeg init ~recc:aux ~p:o#p
	| `Lookahead o -> args#fLookahead init ~recc:aux ~p:o#p
	| `Option o -> args#fOption init ~recc:aux ~p:o#p
	| `Choice o -> args#fChoice init ~recc:aux ~p1:o#p1 ~p2:o#p2
	| `Concat o -> args#fConcat init ~recc:aux ~p:o#p ~names:o#names ~action:o#action
	| `Nonterm o -> args#fNonterm init ~recc:aux ~nonterm:o#nonterm ~params:o#params
	| `External o -> args#fExternal init ~recc:aux ~nonterm:o#nonterm ~params:o#params
	| `Empty o -> args#fEmpty init
	| `Void o -> args#fVoid init
	| `Memo o -> args#fMemo init ~recc:aux ~p:o#p
	| `Param o -> args#fParam init ~i:o#i ~name:o#name
      in
      aux init cur ;;

    (* Map *)

    xtype map_args = `MK
      fAnyChar : { parsePrim } ;
      fCharClass : { chars:ustring -> parsePrim } ;
      fTest : { recc:(parsePrim -> parsePrim) -> p:parsePrim -> test:Camlp4.PreCast.Ast.expr -> parsePrim } ;
      fString : { s:ustring -> parsePrim } ;
      fNeg : {  recc:(parsePrim -> parsePrim) -> p:parsePrim -> parsePrim } ;
      fLookahead : {  recc:(parsePrim -> parsePrim) -> p:parsePrim -> parsePrim } ;
      fOption : {  recc:(parsePrim -> parsePrim) -> p:parsePrim -> parsePrim } ;
      fChoice : {  recc:(parsePrim -> parsePrim) -> p1:parsePrim -> p2:parsePrim -> parsePrim } ;
      fConcat : {  recc:(parsePrim -> parsePrim) -> p:(parsePrim list) -> names:(string option list) -> action:Camlp4.PreCast.Ast.expr -> parsePrim } ;
      fNonterm : { recc:(parsePrim -> parsePrim) -> nonterm:ident -> params:(parsePrim list) -> parsePrim } ;
      fExternal : { recc:(parsePrim -> parsePrim) -> nonterm:ident -> params:(parsePrim list) -> parsePrim } ;
      fEmpty : { parsePrim } ;
      fVoid : { parsePrim } ;
      fMemo : { recc:(parsePrim -> parsePrim) -> p:parsePrim -> parsePrim };
      fParam : { i:int -> name:ident -> parsePrim }
      
    ;;

    let map_default =
      let (`MK md) : map_args =
	<{ map_args.MK
	     fAnyChar   = ( <{ AnyChar }> );
  	     fCharClass = ( fun ~chars -> <{ CharClass chars=chars }>  ) ;
	     fTest      = ( fun ~recc ~p ~test -> <{ Test p=recc p; test=test }>  ) ;
	     fString    = ( fun ~s -> <{ String s=s }> ) ;
	     fNeg       = ( fun ~recc ~p -> <{ Neg p=recc p }> ) ;
	     fLookahead = ( fun ~recc ~p -> <{ Lookahead p=recc p }>  ) ;
	     fOption    = ( fun ~recc ~p -> <{ Option p=recc p }>  ) ;
	     fChoice    = ( fun ~recc ~p1 ~p2 -> <{ Choice p1=recc p1; p2=recc p2 }>  ) ;
	     fConcat    = ( fun ~recc ~p ~names ~action -> <{ Concat p=List.map recc p ; names=names; action=action }>  ) ;
	     fNonterm   = ( fun ~recc ~nonterm ~params -> <{ Nonterm nonterm=nonterm ; params=List.map recc params }>  ) ;
	     fExternal  = ( fun ~recc ~nonterm ~params -> <{ External nonterm=nonterm ; params=List.map recc params }>  ) ;
	     fEmpty     = ( <{ Empty }> ) ;
	     fVoid      = ( <{ Void }> ) ;
	     fMemo      = ( fun ~recc ~p -> <{ Memo p = recc p }> ) ;
	     fParam     = ( fun ~i ~name -> <{ Param i = i ; name = name }> )
	 }>
      in md
    ;;

    let (map : map_args -> parsePrim -> parsePrim) (`MK args) (cur : parsePrim) =
      let fold_args =
	<{ fold_args.MK 
	  fAnyChar = ( fun _ -> args#fAnyChar ) ;
	  fCharClass = ( fun _ -> args#fCharClass ) ;
	  fTest = ( fun r ~recc -> args#fTest ~recc:(recc r) ) ;
	  fString = ( fun _ -> args#fString ) ;
	  fNeg = ( fun r ~recc -> args#fNeg ~recc:(recc r) ) ;
	  fLookahead = ( fun r ~recc -> args#fLookahead ~recc:(recc r) ) ;
	  fOption = ( fun r ~recc -> args#fOption ~recc:(recc r) ) ;
	  fChoice = ( fun r ~recc -> args#fChoice ~recc:(recc r) ) ;
	  fConcat = ( fun r ~recc -> args#fConcat ~recc:(recc r) ) ;
	  fNonterm = ( fun r ~recc -> args#fNonterm ~recc:(recc r) ) ;
	  fExternal = ( fun r ~recc -> args#fExternal ~recc:(recc r) );
	  fEmpty = ( fun _ -> args#fEmpty ) ;
	  fVoid = ( fun _ -> args#fVoid ) ;
	  fMemo = ( fun r ~recc -> args#fMemo ~recc:(recc r) ) ;
	  fParam = ( fun _ -> args#fParam ) }>
      in
      fold fold_args cur cur
    ;;

 
   (* Iter *)

    xtype iter_args = `MK
      fAnyChar : { unit -> unit } ;
      fCharClass : { chars:ustring -> unit } ;
      fTest : { recc:(parsePrim -> unit) -> p:parsePrim -> test:Camlp4.PreCast.Ast.expr -> unit } ;
      fString : { s:ustring -> unit } ;
      fNeg : {  recc:(parsePrim -> unit) -> p:parsePrim -> unit } ;
      fLookahead : {  recc:(parsePrim -> unit) -> p:parsePrim -> unit } ;
      fOption : {  recc:(parsePrim -> unit) -> p:parsePrim -> unit } ;
      fChoice : {  recc:(parsePrim -> unit) -> p1:parsePrim -> p2:parsePrim -> unit } ;
      fConcat : {  recc:(parsePrim -> unit) -> p:(parsePrim list) -> names:(string option list) -> action:Camlp4.PreCast.Ast.expr -> unit } ;
      fNonterm : { recc:(parsePrim -> unit) -> nonterm:ident -> params:(parsePrim list) -> unit } ;
      fExternal : { recc:(parsePrim -> unit) -> nonterm:ident -> params:(parsePrim list) -> unit } ;
      fEmpty : { unit -> unit } ;
      fVoid : { unit -> unit } ;
      fMemo : { recc:(parsePrim -> unit) -> p:parsePrim -> unit };
      fParam : { i:int -> name:ident -> unit }
    ;;

    let iter_default =
      let (`MK id) : iter_args = 
	<{ iter_args.MK
	     fAnyChar   = ( fun () -> () );
	     fCharClass = ( fun ~chars -> () ) ;
	     fTest      = ( fun ~recc ~p ~test -> recc p ) ;
	     fString    = ( fun ~s -> () ) ;
	     fNeg       = ( fun ~recc ~p -> recc p ) ;
	     fLookahead = ( fun ~recc ~p -> recc p ) ;
	     fOption    = ( fun ~recc ~p -> recc p ) ;
	     fChoice    = ( fun ~recc ~p1 ~p2 -> recc p1 ; recc p2 ) ;
	     fConcat    = ( fun ~recc ~p ~names ~action -> List.iter recc p ) ;
	     fNonterm   = ( fun ~recc ~nonterm ~params -> List.iter recc params ) ;
	     fExternal  = ( fun ~recc ~nonterm ~params -> List.iter recc params ) ;
	     fEmpty     = ( fun () -> () ) ;
	     fVoid      = ( fun () -> () ) ;
	     fMemo      = ( fun ~recc ~p -> recc p );
	     fParam     = ( fun ~i ~name -> () )
	 }>
      in id ;;

    let (iter : iter_args -> parsePrim -> unit) (`MK args) (cur : parsePrim) =
      let fold_args =
	<{ fold_args.MK 
	     fAnyChar   = ( args#fAnyChar ) ;
	     fCharClass = ( fun _ -> args#fCharClass ) ;
	     fTest      = ( fun r ~recc -> args#fTest ~recc:(recc ()) ) ;
	     fString    = ( fun _ -> args#fString ) ;
	     fNeg       = ( fun r ~recc -> args#fNeg ~recc:(recc ()) ) ;
	     fLookahead = ( fun r ~recc -> args#fLookahead ~recc:(recc ()) ) ;
	     fOption    = ( fun r ~recc -> args#fOption ~recc:(recc ()) ) ;
	     fChoice    = ( fun r ~recc -> args#fChoice ~recc:(recc ()) ) ;
	     fConcat    = ( fun r ~recc -> args#fConcat ~recc:(recc ()) ) ;
	     fNonterm   = ( fun r ~recc -> args#fNonterm ~recc:(recc ()) ) ;
	     fExternal  = ( fun r ~recc -> args#fExternal ~recc:(recc ()) ) ;
	     fEmpty     = ( args#fEmpty ) ;
	     fVoid      = ( args#fVoid ) ;
	     fMemo      = ( fun r ~recc -> args#fMemo ~recc:(recc ()) ) ;
	     fParam     = ( fun _ -> args#fParam )
	 }>
      in
      fold fold_args () cur
    ;;

    

  end;;

let _ADD_PROFILING_CODE = false ;;
let _ALLOW_LEFT_RECURSION = false ;;

(* make it easy to construct grammars *)

module PEGshort =
  struct

    let alist_to_idmap l = IdentMap.of_enum (List.enum l)

    let ur s = UString.of_string s;;
    let s_to_id s = <{ Id id = ur s }> ;;
    let memo p  = <{ Memo p = p }> ;;
    let optmemo opt p = match opt with Some _ -> memo p | None -> p ;;

    let n id = <{ Nonterm nonterm = s_to_id id ; params = [] }> ;;
    let nM id = memo <{ Nonterm nonterm = s_to_id id ; params = [] }> ;;
    let nP id params = <{ Nonterm nonterm = s_to_id id ; params = params }> ;;
    let nPM id params = memo <{ Nonterm nonterm = s_to_id id ; params = params }> ;;
    let wild = <{ AnyChar }> ;;
    let c s  = 
      let unicode = ur s in
      let unicode' = 
	(* TODO: move ] to the end if it exists, so that printing/parsing works correctly.
	   currently UString.sub is buggy, so I'm not doing this yet *)
	unicode
      in
      <{ CharClass chars = unicode' }> ;;
    let s s  = <{ String s = ur s }> ;;
    let neg p = <{ Neg p = p }> ;;
    let ahd p = <{ Lookahead p = p }> ;;
    let opt p = <{ Option p = p }> ;;
    let (//) p1 p2 = <{ Choice p1 = p1 ; p2 = p2 }> ;;
    let epsilon = <{ Empty }> ;;
    let void    = <{ Void }> ;;
    let test p what = <{ Test p = p ; test = what }> ;;
    let p i     = <{ Param i = i; name = s_to_id "" }> ;;

    let choices ps =
      match ps with
	  [] -> <{ Empty }>
	| hd :: [] -> hd
	| hd :: tl -> List.fold_left (fun p1 p2 -> <{ Choice p1 = p1 ; p2 = p2 }>) hd tl
    let concats (ps, names, action) =
      let _loc = Camlp4.PreCast.Loc.ghost in
      let open Camlp4.PreCast in
      let nameslist = names |> Str.split (Str.regexp " +") in
      match ps, action with
	[], `V | [], `A <:expr< () >> -> epsilon
      | [hd], `V -> hd
      | ps, action ->
	
	<{ Concat
	   p = ps ;
	   names = nameslist |> List.map (fun s -> if s = "_" then None else Some s);
	   action = 
	    match action with
	      `A action -> action
	    | `V ->
	      (let names' =
		 nameslist |> List.filter_map (fun s -> if s = "_" then None else Some <:expr< $lid:s$ >>)
	       in
	       match names' with
		 [] -> <:expr< () >>
	       | [hd] -> <:expr< $hd$ >>
	       | hd::tl -> List.fold_left (fun expr elm -> <:expr< ($expr$, $elm$) >>) hd tl) }>
    ;;

    let fixnt (internal : unit IdentMap.t) (paramslist : string list) prod = 
      let open ParsePrim in
      prod |> 
	  map <{ map_args.MK .. = map_default ;
	         fNonterm = ( fun ~recc ~nonterm:((`Id o) as nonterm) ~params -> 
		   match List.index_of (o#id |> UString.to_string) paramslist with
		     Some i ->
		       (if List.is_empty params then <{ Param i = i; name = nonterm }>
		        else failwith ("parameter " ^ (o#id |> UString.to_string) ^
					  " used as a parametric parser, which is not allowed"))
		   | None -> 
		     if (IdentMap.mem nonterm internal) then
		       <{ Nonterm nonterm = nonterm ; params = List.map recc params }> 
		     else
		       <{ External nonterm = nonterm ; params = List.map recc params }>
		 ) ;
		 fParam = ( fun ~i ~name -> 
		   <{ Param i = i ; name = List.nth paramslist i |> s_to_id }> )
	       }>
    ;;
    

    let internal_nts list_of_entries =
      let internal : unit IdentMap.t = IdentMap.empty in
      list_of_entries |>
      List.fold_left (fun internal (id,_,_) -> IdentMap.add (s_to_id id) () internal) internal
    ;;


    let peg preamble list_of_entries postamble : pegGrammar =

      let internal = internal_nts list_of_entries in

      let ntdef params list_of_productions =

	let paramslist = params |> Str.split (Str.regexp " +") in
	<{ NonTermDef
	     params = paramslist |> List.map s_to_id ;
	     prod = list_of_productions |> List.map concats |> choices |> fixnt internal paramslist }>

      in
      
      <{ Peg entries =
	  alist_to_idmap
	    (List.map 
	       (fun (id,params,def) -> s_to_id id, ntdef params def)
	       list_of_entries) ;
	 exports =
	  list_of_entries
	   |> List.map (fun (id,params,def) -> (s_to_id id, id))
	   |> alist_to_idmap ;
	 preamble = preamble; postamble = postamble
	       
       }> ;;

    let pegNoDefProds preamble list_of_entries postamble : pegGrammar =

      let internal = internal_nts list_of_entries in

      let ntdef params list_of_productions =

	let paramslist = params |> Str.split (Str.regexp " +") in
	<{ NonTermDef
	     params = paramslist |> List.map s_to_id ;
	     prod = list_of_productions |> fixnt internal paramslist }>
      in
      
      <{ Peg entries =
	  alist_to_idmap
	    (List.map 
	       (fun (id,params,def) -> s_to_id id, ntdef params def)
	       list_of_entries) ;
	 exports =
	  list_of_entries
	   |> List.map (fun (id,params,def) -> (s_to_id id, id))
	   |> alist_to_idmap ;
	 preamble = preamble ; postamble = postamble
       }> ;;
      


  end;;

let updateExternalMemocellsInfo l =
  needed_memocells_external :=
    List.fold_left (fun needed (s,what) -> IdentMap.add (PEGshort.s_to_id s) what needed) !needed_memocells_external l
;;


(* (not so)pretty printer for PEG grammars
   meant primarily to be used to generate bootstrapping PEG grammar from Ocaml-coded PEG grammar *)
module PegPrint =
  struct
    let exprAST_to_string expr =
      let module ExportAst = struct
	open Camlp4_import.Parsetree;;
	open Lexing;;
	open Camlp4;;
	open PreCast;;
	open Camlp4.Sig;;
	module Ast2pt = Camlp4.Struct.Camlp4Ast2OCamlAst.Make(Ast);;
	module Lexer = Camlp4.Struct.Lexer.Make(Token);;
	module Printer = Camlp4.Printers.OCaml.Make(Camlp4.PreCast.Syntax);;
	module Dumper = Camlp4.Printers.DumpOCamlAst.Make(Camlp4.PreCast.Syntax);;
	
	let printer = (new Printer.printer ())#expr
      end
      in
      ExportAst.printer Format.str_formatter expr;
      Format.flush_str_formatter ()
    ;;

    let printer_ident oc (`Id id) = Printf.fprintf oc "%a" UString.print id#id ;;
    let printer_ast oc expr = Printf.fprintf oc "<< %s >>" (exprAST_to_string expr) ;;
    let printer_ast_dummy oc expr = () ;;
    let printer_params recc oc params =
      if not (List.is_empty params) then
	Printf.fprintf oc "%a"
	  (List.print ~first:"(" ~last:")" ~sep:", " recc) params ;;
    let printer_paramdef oc params = 
      if not (List.is_empty params) then
	Printf.fprintf oc "%a"
	  (List.print ~first:"(" ~last:")" ~sep:", " printer_ident) params ;;
    let print_escaped oc us = Printf.fprintf oc "%a" UString.print (UString.escaped us) ;;

    let printer_parsePrim_param ?(printFull = true) oc (p : parsePrim) =
	let open ParsePrim in
	let args =
	  <{ iter_args.MK .. = iter_default ;
	     fAnyChar   = ( fun () -> Printf.fprintf oc "." ) ;
	     fCharClass = ( fun ~chars -> Printf.fprintf oc "[%a]" print_escaped chars );
	     fTest      = ( fun ~recc ~p ~test ->
	                           Printf.fprintf oc "&&( %a %a )" (fun _ -> recc) p printer_ast test );
	     fString    = ( fun ~s -> Printf.fprintf oc "\"%a\"" print_escaped s );
	     fNeg       = ( fun ~recc ~p -> Printf.fprintf oc "!%a" (fun _ -> recc) p );
	     fLookahead = ( fun ~recc ~p -> Printf.fprintf oc "&%a" (fun _ -> recc) p );
	     fOption    = ( fun ~recc ~p -> Printf.fprintf oc "?%a" (fun _ -> recc) p );
	     fChoice    = ( fun ~recc ~p1 ~p2 -> Printf.fprintf oc "(%a\n\t/ %a)" (fun _ -> recc) p1 (fun _ -> recc) p2 );
	     fConcat    = ( fun ~recc ~p ~names ~action ->
	       Printf.fprintf oc "(";
	       List.iter2 
		 (fun p -> function Some name when printFull -> Printf.fprintf oc "%s:%a " name (fun _ -> recc) p
		                  | _ -> Printf.fprintf oc "%a " (fun _ -> recc) p)
		 p names ;
	       Printf.fprintf oc "%a)" (if printFull then printer_ast else printer_ast_dummy) action );
	     fNonterm   = ( fun ~recc ~nonterm ~params ->
	       Printf.fprintf oc "%a%a" printer_ident nonterm (printer_params (fun _ -> recc)) params);
	     fExternal  = ( fun ~recc ~nonterm ~params ->
	       Printf.fprintf oc "%a%a" printer_ident nonterm (printer_params (fun _ -> recc)) params);
	     fEmpty     = ( fun () -> () );
	     fVoid      = ( fun () -> Printf.fprintf oc "fail" );
	     fMemo      = ( fun ~recc ~p -> Printf.fprintf oc "(%a)^" (fun _ -> recc) p ) ;
	     fParam     = ( fun ~i ~name -> Printf.fprintf oc "%a" printer_ident name)
	   }>
	in
	iter args p
    ;;

    let printer_parsePrim oc p = printer_parsePrim_param ~printFull:true oc p;;

    let printer oc ((`Peg peg) : pegGrammar) =
      
      let print_def ntident (`NonTermDef ntdef) =

	Printf.fprintf oc "%a%a -> \n\t  %a;\n"
	  printer_ident ntident
	  printer_paramdef ntdef#params
	  printer_parsePrim ntdef#prod

      in
      
      IdentMap.iter print_def peg#entries
    
  end;;


module ParsePrimHashed =
  struct
    type t = parsePrim

    let equal (p1 : parsePrim) (p2 : parsePrim) =
      let _loc = Camlp4.PreCast.Loc.ghost in
      let open Camlp4.PreCast.Ast in
      let rec norm p =
	match p with
	    `Memo o -> norm o#p
	  | _ -> p
      in
      
      let rec aux p1 p2 =
	match norm p1, norm p2 with
	  (`AnyChar _), (`AnyChar _) -> true
	| (`CharClass o1), (`CharClass o2) -> UString.compare o1#chars o2#chars == 0
	| (`Test o1), (`Test o2) -> (aux o1#p o2#p) && (o1#test = o2#test)
	| (`String o1), (`String o2) -> UString.compare o1#s o2#s == 0
	| (`Neg o1), (`Neg o2) -> aux o1#p o2#p
	| (`Lookahead o1), (`Lookahead o2) -> aux o1#p o2#p
	| (`Option o1), (`Option o2) -> aux o1#p o2#p
	| (`Choice o1), (`Choice o2) -> (aux o1#p1 o2#p1) && (aux o1#p2 o2#p2)
	| (`Concat o1), (`Concat o2) -> List.for_all2 aux o1#p o2#p
	| (`Nonterm o1), (`Nonterm o2) -> (IdentOrdered.compare o1#nonterm o2#nonterm == 0) && (List.for_all2 aux o1#params o2#params)
	| (`External o1), (`External o2) -> (IdentOrdered.compare o1#nonterm o2#nonterm == 0) && (List.for_all2 aux o1#params o2#params)
	| (`Empty _), (`Empty _) -> true
	| (`Void _), (`Void _) -> true
	| (`Param o1), (`Param o2) -> o1#i == o2#i
	| _, _ -> false
      in
      aux p1 p2;;


    let hash p =
      let outstr = IO.output_string () in
      PegPrint.printer_parsePrim_param ~printFull:false outstr p;
      IO.close_out outstr |>  Hashtbl.hash

  end;;

(* Real code actually begins *)

module NontermTable =
  UniqueTable.Make(struct
    type t = ident ;;
    let equal (`Id r1) (`Id r2) = (UString.compare r1#id r2#id) == 0 ;;
    let hash (`Id r) = r#id |> Hashtbl.hash ;;
  end) ;;

module ParsePrimTable = UniqueTable.Make(ParsePrimHashed) ;;
module ParsePrimHashtbl = StdHashtbl.Make(ParsePrimHashed) ;;
module ParsePrimHashSet = StdHashtbl.Make(ParsePrimHashed) ;;
type parsePrimHashSet = unit ParsePrimHashSet.t ;;


open Camlp4;;
open PreCast;;

let list_to_expr l =
  let _loc = Loc.ghost in
  List.fold_left (fun tl hd -> <:expr< $hd$ :: $tl$ >>) <:expr< [] >> l
;;


let (recursive_decoupling : nonterminalDef identMap -> NontermTable.t -> nonterminalDef identMap list) ntdefs nthash =
  
  let module Node =
      struct
	open NontermTable
	type t = uobj
	let hash uobj = uobj.hcode
	let compare i1 i2 = Pervasives.compare i1.tag i2.tag
	let to_string uobj = let (`Id id) = uobj.obj in UString.to_string id#id
      end
  in
  let module G = Graph.Make(Node) in
  let open G in
  
  let (identToNode : ident -> Node.t) = NontermTable.uobj nthash in
  let (nodeToIdent : Node.t -> ident) n = let open NontermTable in n.obj in

  let nodes = IdentMap.keys ntdefs |> Enum.map identToNode |> List.of_enum in

  let (getDependencies : nonterminalDef -> NodeSet.t) (`NonTermDef o) =

    let open ParsePrim in
    let deps =
      fold 
      <{ fold_args.MK
	   fNonterm =
 	    (fun deps ~recc ~nonterm ~params ->
	      List.fold_left recc (NodeSet.add (identToNode nonterm) deps) params) ;
	 .. = fold_default
       }>
      NodeSet.empty o#prod
    in
    deps

  in

  let ( *** ) f g (x,y) = (f x, g y) in
  let dependencies : NodeSet.t NodeMap.t =
    IdentMap.bindings ntdefs
      |> List.map (identToNode *** getDependencies)
      |> List.enum |> NodeMap.of_enum
  in
(*
  let _ =
    IdentMap.bindings ntdefs
      |> List.map (id *** getDependencies)
      |> Printf.printf "input deps\n%a\n" (List.print (Pair.print PegPrint.printer_ident G.printer_nodeset))
  in
*)


  let depgraph = reverse { nodes = nodes ; edges = dependencies } in
  let partitions = cyclic_topo_sort depgraph in
  let result =
    partitions |>
	List.map (fun nodes ->
	  NodeSet.fold
	    (fun node newntdefs -> 
	      let ident = nodeToIdent node in
	      IdentMap.add ident (IdentMap.find ident ntdefs) newntdefs)
	    nodes IdentMap.empty)
  in
  result

;;



let subst_params expr params =
  let open ParsePrim in
  map <{ map_args.MK .. = map_default ; fParam = (fun ~i ~name -> List.nth params i) }> expr ;;

let has_param expr =
  let open ParsePrim in
  fold <{ fold_args.MK .. = fold_default ; fParam = (fun r ~i ~name -> true) }> false expr ;;

let external_needed_cells nonterm params =
  let name = nonterm#!Id#id |> UString.to_string in
  let _ =
    if not (IdentMap.mem nonterm !needed_memocells_external) then
      failwith (Printf.sprintf "Nonterminal %s has not been defined." name)
  in
  (IdentMap.find nonterm !needed_memocells_external
      |> increasing
      |> List.map (fun i -> <{ External params = params ; nonterm = name^"~memo"^(string_of_int i) |> PEGshort.s_to_id }>))
;;


let (calculate_needed_memocells : nonterminalDef identMap -> (parsePrim list) identMap * (int ParsePrimHashtbl.t) identMap) ntdefs =

  let emptyMap = IdentMap.fold (fun k _ map -> IdentMap.add k (ParsePrimHashSet.create 50) map) ntdefs IdentMap.empty in

  let prevNeeds = ref emptyMap in
  let prevChanged = ref false in

  let copyMap oldmap = 
    IdentMap.fold
      (fun k v newmap -> IdentMap.add k (ParsePrimHashSet.copy v) newmap)
      oldmap
      IdentMap.empty
  in
  let (addNeed : parsePrimHashSet identMap -> ident -> parsePrim -> unit) needs id pp =
    let curset = IdentMap.find id needs in
    if not (ParsePrimHashSet.mem curset pp) then
      (ParsePrimHashSet.add curset pp () ;
       prevChanged := true)
  in

  (* step one: each module adds its direct needed memocells *)
  ntdefs |>
  IdentMap.iter
    (fun k (`NonTermDef o) ->
      o#prod |> 
	  let open ParsePrim in
	  iter <{ iter_args.MK .. = iter_default ;
		     fMemo = ( fun ~recc ~p -> recc p; if has_param p then addNeed !prevNeeds k p ) ;
		     fExternal = ( fun ~recc ~nonterm ~params ->
		                   List.iter recc params ;
		                   let _ =
				     if not (IdentMap.mem nonterm !prevNeeds) then
				       prevNeeds := IdentMap.add nonterm (ParsePrimHashSet.create 50) !prevNeeds
				   in
				   let paramsId =
				     increasing (List.length params) |>
				     List.map (fun i -> <{ Param i = i ; name = "_"^(string_of_int i) |> PEGshort.s_to_id }>)
				   in
		                   external_needed_cells nonterm paramsId |> List.iter (addNeed !prevNeeds nonterm)
		                 )
		}> );

  (* step two through N: each module adds the needed memocells of its dependencies *)
  while !prevChanged do
    (prevChanged := false;
     let newNeeds = copyMap !prevNeeds in
     IdentMap.iter
       (fun k (`NonTermDef o) ->
	 o#prod |>
	     let open ParsePrim in
	     let addmore = 
	       ( fun ~recc ~nonterm ~params ->
		 List.iter recc params;
		 if List.exists has_param params then
		   (IdentMap.find nonterm !prevNeeds |>
		       ParsePrimHashSet.iter
				      (fun need _ -> let substNeed = subst_params need params in
						     if has_param substNeed then
						       addNeed newNeeds k substNeed)) )
	     in
	     iter <{ iter_args.MK .. = iter_default ;
		        fNonterm = addmore; fExternal = addmore }>)
		           
       ntdefs;
     prevNeeds := newNeeds)
   done;

  let needsAsList =
  !prevNeeds |>
      IdentMap.map (fun hash -> ParsePrimHashSet.fold (fun k _ l -> k :: l) hash [])
  in
  let needsAsHash =
    needsAsList |>
	IdentMap.map
         (fun lst ->
	   let newhash = ParsePrimHashtbl.create 500 in
	   ExtList.iteri (fun i k -> ParsePrimHashtbl.add newhash k i) lst;
	   newhash)
  in
  needsAsList, needsAsHash
;;

(* actual parsing: generation *)
let (parseGen : pegGrammar -> Ast.str_item) grammar =

  let _loc = Loc.ghost in
  let nontermTable = NontermTable.create 500 in
  let parsePrimTable = ParsePrimTable.create 500 in

  let `Peg peg = grammar in
  let mutual_rec_blocks = recursive_decoupling peg#entries nontermTable in
  let memo_needs_list, memo_needs_map = calculate_needed_memocells peg#entries in

(*
  let _ =
    IdentMap.bindings memo_needs_list |>
    List.map (fun (id, ps) -> Printf.printf "%a needs %a\n" PegPrint.printer_ident id (List.print PegPrint.printer_parsePrim) ps)
  in
*)

  let parse_func_name (`Id id) =
    "_parse_"
      (* ^ (ntid |> NontermTable.uniqueTag nontermTable |> string_of_int) ^ "_" *)
      ^ (id#id |> UString.to_string)
  in
  let param_name i = "_param_" ^ (string_of_int i) in

  let memocell_of ntid (prim : parsePrim) =
    if has_param prim then 
      (let i = ParsePrimHashtbl.find (IdentMap.find ntid memo_needs_map) prim in
       let stri = string_of_int i in
       <:expr< List.nth _memocells $int:stri$ >>)
    else
      (let i = ParsePrimTable.uniqueTag parsePrimTable prim in
       let stri = string_of_int i in
       <:expr< Memotable.get_memocell !_memotable $int:stri$ >>)
  in


  let rec genPrim (ntid : ident) (prim : parsePrim) =

    match prim with

      `AnyChar o ->
	<:expr< UChannel.get_one _input >>

      | `CharClass o ->
	let chars = o#chars |> UString.ast_of_ustring _loc in
	<:expr< match UChannel.get_one _input with
                  Some (_head, _input) when UString.contains $chars$ _head ->
                    Some (_head, _input)
                | _ -> None >>

      | `Test o ->
	let pres = genPrim ntid o#p in
	let test = o#test in
	<:expr< match $pres$ with
                  Some (_res, _) when ($test$ _res) -> Some ((), _input)
                | _ -> None >> 

      | `String o ->
	let ps =
	  o#s |> UString.explode |>
	  List.map (fun c -> <{ CharClass chars = UString.implode [c] }>)
	in
	let names =
	  List.map (fun _ -> None) ps
	in
	let action =
	  let strng = o#s |> UString.ast_of_ustring _loc in
	  strng
	in
	let p' =
	  <{ Concat p = ps; names = names; action = action }>
	in
	genPrim ntid p'

      | `Neg o ->
	let pres = genPrim ntid o#p in
	<:expr< match $pres$ with
                  Some _ -> None
                | None -> Some( (), _input ) >>

      | `Lookahead o ->
	let pres = genPrim ntid o#p in
	<:expr< match $pres$ with
                  Some (_res, _) -> Some( _res, _input )
                | None -> None >>

      | `Option o ->
	let pres = genPrim ntid o#p in
	<:expr< match $pres$ with
                 Some (_res, _tail) -> Some ( Some _res, _tail )
               | None -> Some( None, _input ) >>

      | `Choice o ->
	let pres1 = genPrim ntid o#p1 in
	let pres2 = genPrim ntid o#p2 in
	<:expr< match $pres1$ with
                 Some a -> Some a
               | None -> $pres2$ >>

      | `Concat o ->
	let expr_with_hole =
	  List.fold_left2
	    (fun curexpr name p ->
	      let pres = genPrim ntid p in
	      let name = match name with None -> "_" | Some s -> s in
	      (fun hole ->
		curexpr
	        <:expr< match $pres$ with
                          Some ($lid:name$, _input) -> $hole$
                        | None -> None >>))
	    (fun hole -> hole) o#names o#p
	in
	let action = o#action in
	expr_with_hole <:expr< Some ( $action$, _input ) >>

      | `Nonterm o ->
	
	let memocells =
	  IdentMap.find o#nonterm memo_needs_list
              |> List.map (fun p -> memocell_of ntid (subst_params p o#params))
              |> list_to_expr
	in
	let params head =
	  o#params |>
	      List.fold_left (fun head p -> let body = genPrim ntid p in
					    <:expr< $head$ (fun _resetmemo _input -> $body$) >>) head
	in
	let fullparseexpr = 
	  let idmain = parse_func_name o#nonterm in
	  let expr0 = <:expr< $lid:idmain$ >> in
	  let expr1 = params expr0 in
	  <:expr< $expr1$ $memocells$ false _input >>
	in
	fullparseexpr

      | `External o ->

	(* memoization of externals is not handled nicely so far.
	   Assume external parsers P1 and P2 of module M1, called with parameters of module M2.
	   1. We provide memocells coming from M2's memotable to P1 and P2 for M1 expressions involving parameters.
	      That means that M2 parameters will be preserved across calls.
	   2. We reset the memotable for M1 each time that P1 or P2 is called. Therefore M1 memoization is not preserved.
	   3. Assume P1[p] -> (P3[p])^ "A" and P2[p] -> (P3[p])^ "B". Different memocells will be generated for P3[p] in
	      the two cases, even though the same could be used. The reason is that we do not store information about the
	      involved expressions, only about the number of memocells needed.
	   4. Assume P1[a,b] -> P3[a]^ P4[b]^. The calls P1[S1,S2] and P1[S1,S3] will not reuse the memocell for P3[a]^.
	      The reason is as above.
	   5. Needed memocells of external functions are stored in an ugly global table.
	*)
	let memocells =
	  external_needed_cells o#nonterm o#params
	      |> List.map (memocell_of ntid)
	      |> list_to_expr
	in
	let params head =
	  o#params |>
	      List.fold_left (fun head p -> let body = genPrim ntid p in
					    <:expr< $head$ (fun _resetmemo _input -> $body$) >>) head
	in
	let fullparseexpr = 
	  let idmain = "parse_" ^ (o#nonterm#!Id#id |> UString.to_string) in
	  let expr0 = <:expr< $lid:idmain$ >> in
	  let expr1 = params expr0 in
	  <:expr< $expr1$ $memocells$ true _input >>
	in
	fullparseexpr


      | `Memo o ->
	let pres = genPrim ntid o#p in
	let memocell = memocell_of ntid o#p in
	<:expr< let _memocell = $memocell$ in
                match Memotable.find_in_memocell _memocell (UChannel.offset _input) with
                    None -> (let _res = $pres$ in
                             let _res' = match _res with
                                           Some (_actionres, _input) -> Some (Obj.repr _actionres, _input)
                                         | None -> None
                             in
                             Memotable.add_in_memocell _memocell (UChannel.offset _input) _res';
                             _res)
                  | Some (Some (_res, _input)) -> Some (Obj.obj _res, _input)
                  | Some None -> None >>

      | `Param o ->
	let var = param_name o#i in 
	<:expr< $lid:var$ false _input >>

      | `Empty _ ->
	<:expr< Some( (), _input ) >>

      | `Void _ ->
	<:expr< None >>

  in
  
  let functions_for_mutual_rec_block ntdefs =
    
    let bindingAST =
      ntdefs |> IdentMap.bindings |>
 	  List.map (fun (ntname, `NonTermDef ntdef) ->
	    (ntname, 
	     parse_func_name ntname,
	     List.map (fun i -> param_name i) (ntdef#params |> List.length |> increasing),
	     genPrim ntname ntdef#prod)) |>
          List.map (fun (name, funcname, funcparams, funcbody) ->
	    let stateid  = NontermTable.uniqueTag nontermTable name |> string_of_int in
	    let funcbody =
	      if List.length funcparams > 0 || not (_ALLOW_LEFT_RECURSION)
	      then
	      <:expr< fun _memocells _resetmemo _input ->
		       if _resetmemo then ( _memotable := memotable_default () ; LRHash.clear _lrinfo );
                       $funcbody$
              >>
	      else
	      <:expr< fun _memocells _resetmemo _input ->
		       if _resetmemo then ( _memotable := memotable_default () ; LRHash.clear _lrinfo );
                       let _lrkey = $int:stateid$, UChannel.offset _input in
                       if LRHash.mem _lrinfo _lrkey then
                         begin
                           let _used, _res = LRHash.find _lrinfo _lrkey in
                           _used := true;
                           castLR !_res
                         end
                       else
                         begin
                           let _used, _resPrev = ref false, ref None in
                           LRHash.add _lrinfo _lrkey (_used, _resPrev);
                           let _res = growLR _used _resPrev (fun () -> $funcbody$) in
                           LRHash.remove _lrinfo _lrkey;
                           _res
                        end
              >>
	    in
	    let funcbody =
	      if String.ends_with funcname "BM" then
		<:expr< fun _memocells _resetmemo _input ->
                        Benchmark.cumulative $str:funcname$
                        (lazy($funcbody$ _memocells _resetmemo _input)) >>
	      else
		funcbody
	    in
	    let funcbody =
	      if _ADD_PROFILING_CODE then
	      <:expr< fun _memocells _resetmemo _input ->
                      if !_profile then print_string ("$$ " ^ $str:funcname$ ^ " " ^ ( string_of_int (UChannel.offset _input) ) ^ "\n") ;
                      $funcbody$ _memocells _resetmemo _input >>
	      else
		funcbody
	    in
	    let funcbody' = List.fold_left (fun expr param -> <:expr< fun $lid:param$ -> $expr$ >> ) funcbody (List.rev funcparams) in
	    <:binding< $lid:funcname$ = $funcbody'$ >> )
    in
    let bindingHD, bindingTL = List.hd bindingAST, List.tl bindingAST in
    bindingTL |>
	List.fold_left (fun cur elm -> <:binding< $cur$ and $elm$ >>) bindingHD

  in

  let all_functions =
    mutual_rec_blocks
      |> List.fold_left (fun kexpr ntdefs rest ->
	   let fs = functions_for_mutual_rec_block ntdefs in
	   kexpr <:expr< let rec $fs$ in $rest$ >> )
	  (fun rest -> rest)
  in

  let exportpat, exportbody = 

    let exportnames, exportbodies = 

      peg#exports |> IdentMap.bindings |>

	List.fold_left (fun (exportnames, exportbodies) (ntname,  exportname) ->
	  let funcname = parse_func_name ntname in
	  let funcbodyBase = <:expr< $lid:funcname$ >> in
	  ("parse_" ^ exportname) :: exportnames , 
	  funcbodyBase :: exportbodies) ([], [])
    in
    
    List.fold_left2 (fun (exportpat, exportbody) curname curbody  ->
	  ( <:patt< $lid:curname$, $exportpat$ >>, <:expr< $curbody$, $exportbody$ >> ))
      ( <:patt< _ >> , <:expr< () >> ) exportnames exportbodies
  in

  let body = all_functions exportbody in
  let preamble = match peg#preamble with Some s -> s | _ -> <:str_item< >> in
  let postamble = match peg#postamble with Some s -> s | _ -> <:str_item< >> in
  let needed_external = 
      peg#exports |> IdentMap.keys |> Enum.map
	  (fun exportname ->
	    let needed = IdentMap.find exportname memo_needs_list |> List.length in
	    exportname#!Id#id |> UString.to_string, needed) |> List.of_enum
			
  in
  
  let needed_external_ast =
    needed_external
	|> List.map (fun (a,b) -> let b = string_of_int b in <:expr< $str:a$, $int:b$ >>)
	|> list_to_expr
  in
      
  updateExternalMemocellsInfo needed_external ;
  <:str_item< 
    $preamble$
    open PegRuntime ;;

    let _memotable : (Obj.t * UChannel.t) option Memotable.t ref = ref (memotable_default()) ;;
    let _lrinfo     = lrinfo_default() ;;
    let _profile    = ref false ;;
    let $exportpat$ = $body$ ;;
    let () = Peg.updateExternalMemocellsInfo $needed_external_ast$ ;;
    $postamble$
  >>

;;



(* auxiliary definitions, to make the generated parsers easier to use *)

(* type of a parameterless generated parsing function yielding 'res *)
type 'res parser_t = ((Obj.t * UChannel.t) option PegRuntime.Memotable.memocell ref list -> bool ->
		      UChannel.t -> ('res * UChannel.t) option) ;;


let peg_to_file s g = File.with_file_out s (fun oc -> PegPrint.printer oc g) ;;

let string_of_peg g =
  let outstr = IO.output_string () in
  PegPrint.printer outstr g;
  IO.close_out outstr ;;

exception IncompleteParse of UChannel.t * string

let getFullParse result = 
  match result with
    Some(realresult, uc) -> 
      (match UChannel.get_one uc with
	  Some _ -> raise (IncompleteParse (uc, UChannel.string_of_loc (UChannel.loc uc)))
	| None -> realresult)
  | None -> failwith "failed to parse" ;;

let parse_of_string ?initloc parsefunc s =
  UChannel.from_string ?initloc:initloc s |> parsefunc [] true |> getFullParse ;;

let parse_of_file   parsefunc s =
  UChannel.from_filename s |> parsefunc [] true |> getFullParse ;;  

let parse_of_uchannel parsefunc u =
  u |> parsefunc [] true ;;

let option_parse_of_string parsefunc s =
  UChannel.from_string s |> parsefunc [] true ;;


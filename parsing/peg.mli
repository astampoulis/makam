(* PEG Parser generator for OCaml.
   Copyright (c) Antonis Stampoulis 2011 -- 
   Part of the Makam distribution.
   Licensed under the GPLv3. *)
(* This file depends on the xtype OCaml syntactic extension.
   If you make any changes, you need to install xtype and call Camlp4
   to write out the expanded version:
     - go to ../ocamlsyntax/xtype
     - do make && make install
     - now run ./expand-syntax in this directory.
   
   I expect that changes in this file are going to be infrequent;
   we are in the process of getting rid of OCaml-based parsing anyway.
   Also, the use of xtype is not really needed here (it is meant to be useful
   in situations where new constructors are going to be added in types, which
   does not happen here). In the future we will rewrite this code so as not
   to depend on it. 
*)
open Batteries
  
open UChar
  
open Utils
  
type ustring = UString.t

type ident = [ | `Id of < id : ustring > ]

module IdentMap : Map.S with type key = ident
  
type 'a identMap = 'a IdentMap.t

val updateExternalMemocellsInfo : (string * int) list -> unit
  
type parsePrim =
  [
    | `AnyChar of < >
    | `CharClass of < chars : ustring >
    | `Test of < test : Camlp4.PreCast.Ast.expr; p : parsePrim >
    | `String of < s : ustring >
    | `Neg of < p : parsePrim >
    | `Lookahead of < p : parsePrim >
    | `Option of < p : parsePrim >
    | `Choice of < p2 : parsePrim; p1 : parsePrim >
    | `Concat of
                 < action : Camlp4.PreCast.Ast.expr;
                   names : (string option) list; p : parsePrim list
                 >
    | `Nonterm of < params : parsePrim list; nonterm : ident >
    | `External of < params : parsePrim list; nonterm : ident >
    | `Empty of < >
    | `Void of < >
    | `Memo of < p : parsePrim >
    | `Param of < name : ident; i : int >
  ]

type nonterminalDef =
  [ | `NonTermDef of < prod : parsePrim; params : ident list >
  ]

type pegGrammar =
  [
    | `Peg of
              < postamble : Camlp4.PreCast.Ast.str_item option;
                preamble : Camlp4.PreCast.Ast.str_item option;
                exports : string identMap; entries : nonterminalDef identMap
              >
  ]

module PEGshort :
  sig
    val alist_to_idmap : (IdentMap.key * 'a) list -> 'a IdentMap.t
      
    val ur : string -> UString.t
      
    val s_to_id : string -> ident
      
    val n : string -> parsePrim
      
    val nM : string -> parsePrim
      
    val nP : string -> parsePrim list -> parsePrim
      
    val nPM : string -> parsePrim list -> parsePrim
      
    val memo : parsePrim -> parsePrim
      
    val optmemo : 'a option -> parsePrim -> parsePrim
      
    val p : int -> parsePrim
      
    val wild : parsePrim
      
    val c : string -> parsePrim
      
    val s : string -> parsePrim
      
    val neg : parsePrim -> parsePrim
      
    val ahd : parsePrim -> parsePrim
      
    val opt : parsePrim -> parsePrim
      
    val ( // ) : parsePrim -> parsePrim -> parsePrim
      
    val test : parsePrim -> Camlp4.PreCast.Ast.expr -> parsePrim
      
    val choices : parsePrim list -> parsePrim
      
    val concats :
      ((parsePrim list) * string * [ | `A of Camlp4.PreCast.Ast.expr | `V ])
        -> parsePrim
      
    val epsilon : parsePrim
      
    val void : parsePrim
      
    val peg :
      Camlp4.PreCast.Ast.str_item option ->
        (string * string *
         (((parsePrim list) * string * [ | `A of Camlp4.PreCast.Ast.expr | `V
           ]) list))
          list -> Camlp4.PreCast.Ast.str_item option -> pegGrammar
      
    val pegNoDefProds :
      Camlp4.PreCast.Ast.str_item option ->
        (string * string * parsePrim) list ->
          Camlp4.PreCast.Ast.str_item option -> pegGrammar
      
  end
  
module PegPrint :
  sig
    val printer_ident : 'a BatInnerIO.output -> ident -> unit
      
    val printer_ast :
      'a BatInnerIO.output -> Camlp4.PreCast.Syntax.Ast.expr -> unit
      
    val printer_parsePrim_param :
      ?printFull: bool -> 'a BatInnerIO.output -> parsePrim -> unit
      
    val printer_parsePrim : 'a BatInnerIO.output -> parsePrim -> unit
      
    val printer : 'a BatInnerIO.output -> pegGrammar -> unit
      
  end
  
val parseGen : pegGrammar -> Camlp4.PreCast.Ast.str_item
  
val peg_to_file : string -> pegGrammar -> unit
  
exception IncompleteParse of UChannel.t * UChannel.loc
  
val getFullParse : ('a * UChannel.t) option -> 'a
  
type 'res parser_t =
  ((((Obj.t * UChannel.t) option) PegRuntime.Memotable.memocell) ref) list ->
    bool -> UChannel.t -> ('res * UChannel.t) option

val string_of_peg : pegGrammar -> string
  
val parse_of_string :
  ?initloc: UChannel.loc -> 'res parser_t -> string -> 'res
  
val parse_of_file : 'res parser_t -> string -> 'res
  
val parse_of_uchannel :
  'res parser_t -> UChannel.t -> ('res * UChannel.t) option
  
val option_parse_of_string :
  'res parser_t -> string -> ('res * UChannel.t) option
  


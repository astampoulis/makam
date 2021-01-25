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
(* Features:

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
open Batteries
  
open UChar
  
open Utils
  
open PegRuntime
  
type ustring = UString.t

(* Identifiers and maps of identifiers *)
type ident = [ | `Id of < id : ustring > ]

module IdentOrdered =
  struct
    type t = ident
    
    let compare =
      function
      | `Id id1 -> (function | `Id id2 -> UString.compare id1#id id2#id)
      
  end
  
module IdentMap = Map.Make(IdentOrdered)
  
type 'a identMap = 'a IdentMap.t

module IdentSet = Set.Make(IdentOrdered)
  
let needed_memocells_external : (int IdentMap.t) ref = ref IdentMap.empty



let ast_of_ustring _loc input =
  let (s, off, bend, algn) = UString.underlying input in
  let open Camlp4.PreCast in
  let (s, off, bend, algn) = (s |> BatUTF8.to_string_unsafe |> String.escaped,
			     off |> BatUTF8.ByteIndex.to_int |> string_of_int,
			     bend |> BatUTF8.ByteIndex.to_int |> string_of_int,
			     if algn then "True" else "False") in
  Ast.ExApp (_loc,
      (Ast.ExId (_loc,
           (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "UString")),
              (Ast.IdLid (_loc, "of_string_unsafe_fast")))))),
        (Ast.ExTup (_loc,
           (Ast.ExCom (_loc, (Ast.ExStr (_loc, s)),
              (Ast.ExCom (_loc, (Ast.ExInt (_loc, off)),
                 (Ast.ExCom (_loc, (Ast.ExInt (_loc, bend)),
                    (Ast.ExId (_loc, Ast.IdUid(_loc, algn))))))))))))
  (*
  <:expr< UString.of_string_unsafe ($str:s$, $int:off$, $int:bend$, $int:len$) >>
  *)
;;


(* PEG grammars *)
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

(* Very-very ugly boilerplate code for parsePrim follows.
   In the future, syntax_xtype should generate these for each xtype. *)
module ParsePrim =
  struct
    (* Mendler-style fold *)
    type 'pr fold_args =
      [
        | `MK of
                 < fParam : 'pr -> i: int -> name: ident -> 'pr;
                   fMemo :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) -> p: parsePrim -> 'pr;
                   fVoid : 'pr -> 'pr; fEmpty : 'pr -> 'pr;
                   fExternal :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) ->
                         nonterm: ident -> params: (parsePrim list) -> 'pr;
                   fNonterm :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) ->
                         nonterm: ident -> params: (parsePrim list) -> 'pr;
                   fConcat :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) ->
                         p: (parsePrim list) ->
                           names: ((string option) list) ->
                             action: Camlp4.PreCast.Ast.expr -> 'pr;
                   fChoice :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) ->
                         p1: parsePrim -> p2: parsePrim -> 'pr;
                   fOption :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) -> p: parsePrim -> 'pr;
                   fLookahead :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) -> p: parsePrim -> 'pr;
                   fNeg :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) -> p: parsePrim -> 'pr;
                   fString : 'pr -> s: ustring -> 'pr;
                   fTest :
                     'pr ->
                       recc: ('pr -> parsePrim -> 'pr) ->
                         p: parsePrim -> test: Camlp4.PreCast.Ast.expr -> 'pr;
                   fCharClass : 'pr -> chars: ustring -> 'pr;
                   fAnyChar : 'pr -> 'pr
                 >
      ]
    
    let fold_default =
      let (`MK fd) =
        (`MK
           (object
              val _const_fParam = fun r ~i ~name -> r
              method fParam = _const_fParam
              val _const_fMemo = fun r ~recc ~p -> recc r p
              method fMemo = _const_fMemo
              val _const_fVoid = fun r -> r
              method fVoid = _const_fVoid
              val _const_fEmpty = fun r -> r
              method fEmpty = _const_fEmpty
              val _const_fExternal =
                fun r ~recc ~nonterm ~params -> List.fold_left recc r params
              method fExternal = _const_fExternal
              val _const_fNonterm =
                fun r ~recc ~nonterm ~params -> List.fold_left recc r params
              method fNonterm = _const_fNonterm
              val _const_fConcat =
                fun r ~recc ~p ~names ~action -> List.fold_left recc r p
              method fConcat = _const_fConcat
              val _const_fChoice = fun r ~recc ~p1 ~p2 -> recc (recc r p1) p2
              method fChoice = _const_fChoice
              val _const_fOption = fun r ~recc ~p -> recc r p
              method fOption = _const_fOption
              val _const_fLookahead = fun r ~recc ~p -> recc r p
              method fLookahead = _const_fLookahead
              val _const_fNeg = fun r ~recc ~p -> recc r p
              method fNeg = _const_fNeg
              val _const_fString = fun r ~s -> r
              method fString = _const_fString
              val _const_fTest = fun r ~recc ~p ~test -> recc r p
              method fTest = _const_fTest
              val _const_fCharClass = fun r ~chars -> r
              method fCharClass = _const_fCharClass
              val _const_fAnyChar = fun r -> r
              method fAnyChar = _const_fAnyChar
            end) :
          'a fold_args)
      in fd
      
    let fold (args : 'a fold_args) (init : 'a) (cur : parsePrim) =
      let (`MK args) = args in
      let rec aux init cur =
        match cur with
        | `AnyChar _ -> args#fAnyChar init
        | `CharClass o -> args#fCharClass init ~chars: o#chars
        | `Test o -> args#fTest init ~recc: aux ~p: o#p ~test: o#test
        | `String o -> args#fString init ~s: o#s
        | `Neg o -> args#fNeg init ~recc: aux ~p: o#p
        | `Lookahead o -> args#fLookahead init ~recc: aux ~p: o#p
        | `Option o -> args#fOption init ~recc: aux ~p: o#p
        | `Choice o -> args#fChoice init ~recc: aux ~p1: o#p1 ~p2: o#p2
        | `Concat o ->
            args#fConcat init ~recc: aux ~p: o#p ~names: o#names
              ~action: o#action
        | `Nonterm o ->
            args#fNonterm init ~recc: aux ~nonterm: o#nonterm
              ~params: o#params
        | `External o ->
            args#fExternal init ~recc: aux ~nonterm: o#nonterm
              ~params: o#params
        | `Empty o -> args#fEmpty init
        | `Void o -> args#fVoid init
        | `Memo o -> args#fMemo init ~recc: aux ~p: o#p
        | `Param o -> args#fParam init ~i: o#i ~name: o#name
      in aux init cur
      
    (* Map *)
    type map_args =
      [
        | `MK of
                 < fParam : i: int -> name: ident -> parsePrim;
                   fMemo :
                     recc: (parsePrim -> parsePrim) ->
                       p: parsePrim -> parsePrim;
                   fVoid : parsePrim; fEmpty : parsePrim;
                   fExternal :
                     recc: (parsePrim -> parsePrim) ->
                       nonterm: ident ->
                         params: (parsePrim list) -> parsePrim;
                   fNonterm :
                     recc: (parsePrim -> parsePrim) ->
                       nonterm: ident ->
                         params: (parsePrim list) -> parsePrim;
                   fConcat :
                     recc: (parsePrim -> parsePrim) ->
                       p: (parsePrim list) ->
                         names: ((string option) list) ->
                           action: Camlp4.PreCast.Ast.expr -> parsePrim;
                   fChoice :
                     recc: (parsePrim -> parsePrim) ->
                       p1: parsePrim -> p2: parsePrim -> parsePrim;
                   fOption :
                     recc: (parsePrim -> parsePrim) ->
                       p: parsePrim -> parsePrim;
                   fLookahead :
                     recc: (parsePrim -> parsePrim) ->
                       p: parsePrim -> parsePrim;
                   fNeg :
                     recc: (parsePrim -> parsePrim) ->
                       p: parsePrim -> parsePrim;
                   fString : s: ustring -> parsePrim;
                   fTest :
                     recc: (parsePrim -> parsePrim) ->
                       p: parsePrim ->
                         test: Camlp4.PreCast.Ast.expr -> parsePrim;
                   fCharClass : chars: ustring -> parsePrim;
                   fAnyChar : parsePrim
                 >
      ]
    
    let map_default =
      let (`MK md) =
        (`MK
           (object
              val _const_fParam =
                fun ~i ~name ->
                  `Param
                    (object
                       val _const_name = name
                       method name = _const_name
                       val _const_i = i
                       method i = _const_i
                     end)
              method fParam = _const_fParam
              val _const_fMemo =
                fun ~recc ~p ->
                  `Memo
                    (object val _const_p = recc p method p = _const_p end)
              method fMemo = _const_fMemo
              val _const_fVoid = `Void (object  end)
              method fVoid = _const_fVoid
              val _const_fEmpty = `Empty (object  end)
              method fEmpty = _const_fEmpty
              val _const_fExternal =
                fun ~recc ~nonterm ~params ->
                  `External
                    (object
                       val _const_params = List.map recc params
                       method params = _const_params
                       val _const_nonterm = nonterm
                       method nonterm = _const_nonterm
                     end)
              method fExternal = _const_fExternal
              val _const_fNonterm =
                fun ~recc ~nonterm ~params ->
                  `Nonterm
                    (object
                       val _const_params = List.map recc params
                       method params = _const_params
                       val _const_nonterm = nonterm
                       method nonterm = _const_nonterm
                     end)
              method fNonterm = _const_fNonterm
              val _const_fConcat =
                fun ~recc ~p ~names ~action ->
                  `Concat
                    (object
                       val _const_action = action
                       method action = _const_action
                       val _const_names = names
                       method names = _const_names
                       val _const_p = List.map recc p
                       method p = _const_p
                     end)
              method fConcat = _const_fConcat
              val _const_fChoice =
                fun ~recc ~p1 ~p2 ->
                  `Choice
                    (object
                       val _const_p2 = recc p2
                       method p2 = _const_p2
                       val _const_p1 = recc p1
                       method p1 = _const_p1
                     end)
              method fChoice = _const_fChoice
              val _const_fOption =
                fun ~recc ~p ->
                  `Option
                    (object val _const_p = recc p method p = _const_p end)
              method fOption = _const_fOption
              val _const_fLookahead =
                fun ~recc ~p ->
                  `Lookahead
                    (object val _const_p = recc p method p = _const_p end)
              method fLookahead = _const_fLookahead
              val _const_fNeg =
                fun ~recc ~p ->
                  `Neg (object val _const_p = recc p method p = _const_p end)
              method fNeg = _const_fNeg
              val _const_fString =
                fun ~s ->
                  `String (object val _const_s = s method s = _const_s end)
              method fString = _const_fString
              val _const_fTest =
                fun ~recc ~p ~test ->
                  `Test
                    (object
                       val _const_test = test
                       method test = _const_test
                       val _const_p = recc p
                       method p = _const_p
                     end)
              method fTest = _const_fTest
              val _const_fCharClass =
                fun ~chars ->
                  `CharClass
                    (object
                       val _const_chars = chars
                       method chars = _const_chars
                     end)
              method fCharClass = _const_fCharClass
              val _const_fAnyChar = `AnyChar (object  end)
              method fAnyChar = _const_fAnyChar
            end) :
          map_args)
      in md
      
    let (map : map_args -> parsePrim -> parsePrim) =
      function
      | `MK args ->
          (fun (cur : parsePrim) ->
             let fold_args =
               `MK
                 (object
                    val _const_fParam = fun _ -> args#fParam
                    method fParam = _const_fParam
                    val _const_fMemo =
                      fun r ~recc -> args#fMemo ~recc: (recc r)
                    method fMemo = _const_fMemo
                    val _const_fVoid = fun _ -> args#fVoid
                    method fVoid = _const_fVoid
                    val _const_fEmpty = fun _ -> args#fEmpty
                    method fEmpty = _const_fEmpty
                    val _const_fExternal =
                      fun r ~recc -> args#fExternal ~recc: (recc r)
                    method fExternal = _const_fExternal
                    val _const_fNonterm =
                      fun r ~recc -> args#fNonterm ~recc: (recc r)
                    method fNonterm = _const_fNonterm
                    val _const_fConcat =
                      fun r ~recc -> args#fConcat ~recc: (recc r)
                    method fConcat = _const_fConcat
                    val _const_fChoice =
                      fun r ~recc -> args#fChoice ~recc: (recc r)
                    method fChoice = _const_fChoice
                    val _const_fOption =
                      fun r ~recc -> args#fOption ~recc: (recc r)
                    method fOption = _const_fOption
                    val _const_fLookahead =
                      fun r ~recc -> args#fLookahead ~recc: (recc r)
                    method fLookahead = _const_fLookahead
                    val _const_fNeg =
                      fun r ~recc -> args#fNeg ~recc: (recc r)
                    method fNeg = _const_fNeg
                    val _const_fString = fun _ -> args#fString
                    method fString = _const_fString
                    val _const_fTest =
                      fun r ~recc -> args#fTest ~recc: (recc r)
                    method fTest = _const_fTest
                    val _const_fCharClass = fun _ -> args#fCharClass
                    method fCharClass = _const_fCharClass
                    val _const_fAnyChar = fun _ -> args#fAnyChar
                    method fAnyChar = _const_fAnyChar
                  end)
             in fold fold_args cur cur)
      
    (* Iter *)
    type iter_args =
      [
        | `MK of
                 < fParam : i: int -> name: ident -> unit;
                   fMemo : recc: (parsePrim -> unit) -> p: parsePrim -> unit;
                   fVoid : unit -> unit; fEmpty : unit -> unit;
                   fExternal :
                     recc: (parsePrim -> unit) ->
                       nonterm: ident -> params: (parsePrim list) -> unit;
                   fNonterm :
                     recc: (parsePrim -> unit) ->
                       nonterm: ident -> params: (parsePrim list) -> unit;
                   fConcat :
                     recc: (parsePrim -> unit) ->
                       p: (parsePrim list) ->
                         names: ((string option) list) ->
                           action: Camlp4.PreCast.Ast.expr -> unit;
                   fChoice :
                     recc: (parsePrim -> unit) ->
                       p1: parsePrim -> p2: parsePrim -> unit;
                   fOption :
                     recc: (parsePrim -> unit) -> p: parsePrim -> unit;
                   fLookahead :
                     recc: (parsePrim -> unit) -> p: parsePrim -> unit;
                   fNeg : recc: (parsePrim -> unit) -> p: parsePrim -> unit;
                   fString : s: ustring -> unit;
                   fTest :
                     recc: (parsePrim -> unit) ->
                       p: parsePrim -> test: Camlp4.PreCast.Ast.expr -> unit;
                   fCharClass : chars: ustring -> unit;
                   fAnyChar : unit -> unit
                 >
      ]
    
    let iter_default =
      let (`MK id) =
        (`MK
           (object
              val _const_fParam = fun ~i ~name -> ()
              method fParam = _const_fParam
              val _const_fMemo = fun ~recc ~p -> recc p
              method fMemo = _const_fMemo
              val _const_fVoid = fun () -> ()
              method fVoid = _const_fVoid
              val _const_fEmpty = fun () -> ()
              method fEmpty = _const_fEmpty
              val _const_fExternal =
                fun ~recc ~nonterm ~params -> List.iter recc params
              method fExternal = _const_fExternal
              val _const_fNonterm =
                fun ~recc ~nonterm ~params -> List.iter recc params
              method fNonterm = _const_fNonterm
              val _const_fConcat =
                fun ~recc ~p ~names ~action -> List.iter recc p
              method fConcat = _const_fConcat
              val _const_fChoice = fun ~recc ~p1 ~p2 -> (recc p1; recc p2)
              method fChoice = _const_fChoice
              val _const_fOption = fun ~recc ~p -> recc p
              method fOption = _const_fOption
              val _const_fLookahead = fun ~recc ~p -> recc p
              method fLookahead = _const_fLookahead
              val _const_fNeg = fun ~recc ~p -> recc p
              method fNeg = _const_fNeg
              val _const_fString = fun ~s -> ()
              method fString = _const_fString
              val _const_fTest = fun ~recc ~p ~test -> recc p
              method fTest = _const_fTest
              val _const_fCharClass = fun ~chars -> ()
              method fCharClass = _const_fCharClass
              val _const_fAnyChar = fun () -> ()
              method fAnyChar = _const_fAnyChar
            end) :
          iter_args)
      in id
      
    let (iter : iter_args -> parsePrim -> unit) =
      function
      | `MK args ->
          (fun (cur : parsePrim) ->
             let fold_args =
               `MK
                 (object
                    val _const_fParam = fun _ -> args#fParam
                    method fParam = _const_fParam
                    val _const_fMemo =
                      fun r ~recc -> args#fMemo ~recc: (recc ())
                    method fMemo = _const_fMemo
                    val _const_fVoid = args#fVoid
                    method fVoid = _const_fVoid
                    val _const_fEmpty = args#fEmpty
                    method fEmpty = _const_fEmpty
                    val _const_fExternal =
                      fun r ~recc -> args#fExternal ~recc: (recc ())
                    method fExternal = _const_fExternal
                    val _const_fNonterm =
                      fun r ~recc -> args#fNonterm ~recc: (recc ())
                    method fNonterm = _const_fNonterm
                    val _const_fConcat =
                      fun r ~recc -> args#fConcat ~recc: (recc ())
                    method fConcat = _const_fConcat
                    val _const_fChoice =
                      fun r ~recc -> args#fChoice ~recc: (recc ())
                    method fChoice = _const_fChoice
                    val _const_fOption =
                      fun r ~recc -> args#fOption ~recc: (recc ())
                    method fOption = _const_fOption
                    val _const_fLookahead =
                      fun r ~recc -> args#fLookahead ~recc: (recc ())
                    method fLookahead = _const_fLookahead
                    val _const_fNeg =
                      fun r ~recc -> args#fNeg ~recc: (recc ())
                    method fNeg = _const_fNeg
                    val _const_fString = fun _ -> args#fString
                    method fString = _const_fString
                    val _const_fTest =
                      fun r ~recc -> args#fTest ~recc: (recc ())
                    method fTest = _const_fTest
                    val _const_fCharClass = fun _ -> args#fCharClass
                    method fCharClass = _const_fCharClass
                    val _const_fAnyChar = args#fAnyChar
                    method fAnyChar = _const_fAnyChar
                  end)
             in fold fold_args () cur)
      
  end
  
let _ADD_PROFILING_CODE = false
  
let _ALLOW_LEFT_RECURSION = false
  
(* make it easy to construct grammars *)
module PEGshort =
  struct
    let alist_to_idmap l = IdentMap.of_enum (List.enum l)
      
    let ur s = UString.of_string s
      
    let s_to_id s =
      `Id (object val _const_id = ur s method id = _const_id end)
      
    let memo p = `Memo (object val _const_p = p method p = _const_p end)
      
    let optmemo opt p = match opt with | Some _ -> memo p | None -> p
      
    let n id =
      `Nonterm
        (object
           val _const_params = []
           method params = _const_params
           val _const_nonterm = s_to_id id
           method nonterm = _const_nonterm
         end)
      
    let nM id =
      memo
        (`Nonterm
           (object
              val _const_params = []
              method params = _const_params
              val _const_nonterm = s_to_id id
              method nonterm = _const_nonterm
            end))
      
    let nP id params =
      `Nonterm
        (object
           val _const_params = params
           method params = _const_params
           val _const_nonterm = s_to_id id
           method nonterm = _const_nonterm
         end)
      
    let nPM id params =
      memo
        (`Nonterm
           (object
              val _const_params = params
              method params = _const_params
              val _const_nonterm = s_to_id id
              method nonterm = _const_nonterm
            end))
      
    let wild = `AnyChar (object  end)
      
    let c s =
      let unicode = ur s in
      let unicode' =
        (* TODO: move ] to the end if it exists, so that printing/parsing works correctly.
	   currently UString.sub is buggy, so I'm not doing this yet *)
        unicode
      in
        `CharClass
          (object val _const_chars = unicode' method chars = _const_chars end)
      
    let s s = `String (object val _const_s = ur s method s = _const_s end)
      
    let neg p = `Neg (object val _const_p = p method p = _const_p end)
      
    let ahd p = `Lookahead (object val _const_p = p method p = _const_p end)
      
    let opt p = `Option (object val _const_p = p method p = _const_p end)
      
    let ( // ) p1 p2 =
      `Choice
        (object
           val _const_p2 = p2
           method p2 = _const_p2
           val _const_p1 = p1
           method p1 = _const_p1
         end)
      
    let epsilon = `Empty (object  end)
      
    let void = `Void (object  end)
      
    let test p what =
      `Test
        (object
           val _const_test = what
           method test = _const_test
           val _const_p = p
           method p = _const_p
         end)
      
    let p i =
      `Param
        (object
           val _const_name = s_to_id ""
           method name = _const_name
           val _const_i = i
           method i = _const_i
         end)
      
    let choices ps =
      match ps with
      | [] -> `Empty (object  end)
      | [ hd ] -> hd
      | hd :: tl ->
          List.fold_left
            (fun p1 p2 ->
               `Choice
                 (object
                    val _const_p2 = p2
                    method p2 = _const_p2
                    val _const_p1 = p1
                    method p1 = _const_p1
                  end))
            hd tl
      
    let concats (ps, names, action) =
      let _loc = Camlp4.PreCast.Loc.ghost
      in
        let open Camlp4.PreCast
        in
          let nameslist = names |> (Str.split (Str.regexp " +"))
          in
            match (ps, action) with
            | ([], `V) | ([], `A (Ast.ExId (_, (Ast.IdUid (_, "()"))))) ->
                epsilon
            | ([ hd ], `V) -> hd
            | (ps, action) ->
                `Concat
                  (object
                     val _const_action =
                       match action with
                       | `A action -> action
                       | `V ->
                           let names' =
                             nameslist |>
                               (List.filter_map
                                  (fun s ->
                                     if s = "_"
                                     then None
                                     else
                                       Some
                                         (Ast.ExId (_loc,
                                            (Ast.IdLid (_loc, s))))))
                           in
                             (match names' with
                              | [] ->
                                  Ast.ExId (_loc, (Ast.IdUid (_loc, "()")))
                              | [ hd ] -> hd
                              | hd :: tl ->
                                  List.fold_left
                                    (fun expr elm ->
                                       Ast.ExTup (_loc,
                                         (Ast.ExCom (_loc, expr, elm))))
                                    hd tl)
                     method action = _const_action
                     val _const_names =
                       nameslist |>
                         (List.map
                            (fun s -> if s = "_" then None else Some s))
                     method names = _const_names
                     val _const_p = ps
                     method p = _const_p
                   end)
      
    let fixnt (internal : unit IdentMap.t) (paramslist : string list) prod =
      let open ParsePrim
      in
        prod |>
          (map
             (`MK
                (object
                   val _const_fMemo = map_default#fMemo
                   method fMemo = _const_fMemo
                   val _const_fVoid = map_default#fVoid
                   method fVoid = _const_fVoid
                   val _const_fEmpty = map_default#fEmpty
                   method fEmpty = _const_fEmpty
                   val _const_fExternal = map_default#fExternal
                   method fExternal = _const_fExternal
                   val _const_fConcat = map_default#fConcat
                   method fConcat = _const_fConcat
                   val _const_fChoice = map_default#fChoice
                   method fChoice = _const_fChoice
                   val _const_fOption = map_default#fOption
                   method fOption = _const_fOption
                   val _const_fLookahead = map_default#fLookahead
                   method fLookahead = _const_fLookahead
                   val _const_fNeg = map_default#fNeg
                   method fNeg = _const_fNeg
                   val _const_fString = map_default#fString
                   method fString = _const_fString
                   val _const_fTest = map_default#fTest
                   method fTest = _const_fTest
                   val _const_fCharClass = map_default#fCharClass
                   method fCharClass = _const_fCharClass
                   val _const_fAnyChar = map_default#fAnyChar
                   method fAnyChar = _const_fAnyChar
                   val _const_fParam =
                     fun ~i ~name ->
                       `Param
                         (object
                            val _const_name =
                              (List.nth paramslist i) |> s_to_id
                            method name = _const_name
                            val _const_i = i
                            method i = _const_i
                          end)
                   method fParam = _const_fParam
                   val _const_fNonterm =
                     fun ~recc ~nonterm: (nonterm) ~params ->
                       let o = match nonterm with | `Id o -> o
                       in
                         match List.index_of (o#id |> UString.to_string)
                                 paramslist
                         with
                         | Some i ->
                             if List.is_empty params
                             then
                               `Param
                                 (object
                                    val _const_name = nonterm
                                    method name = _const_name
                                    val _const_i = i
                                    method i = _const_i
                                  end)
                             else
                               failwith
                                 ("parameter " ^
                                    ((o#id |> UString.to_string) ^
                                       " used as a parametric parser, which is not allowed"))
                         | None ->
                             if IdentMap.mem nonterm internal
                             then
                               `Nonterm
                                 (object
                                    val _const_params = List.map recc params
                                    method params = _const_params
                                    val _const_nonterm = nonterm
                                    method nonterm = _const_nonterm
                                  end)
                             else
                               `External
                                 (object
                                    val _const_params = List.map recc params
                                    method params = _const_params
                                    val _const_nonterm = nonterm
                                    method nonterm = _const_nonterm
                                  end)
                   method fNonterm = _const_fNonterm
                 end)))
      
    let internal_nts list_of_entries =
      let internal : unit IdentMap.t = IdentMap.empty
      in
        list_of_entries |>
          (List.fold_left
             (fun internal (id, _, _) ->
                IdentMap.add (s_to_id id) () internal)
             internal)
      
    let peg preamble list_of_entries postamble : pegGrammar =
      let internal = internal_nts list_of_entries in
      let ntdef params list_of_productions =
        let paramslist = params |> (Str.split (Str.regexp " +"))
        in
          `NonTermDef
            (object
               val _const_prod =
                 ((list_of_productions |> (List.map concats)) |> choices) |>
                   (fixnt internal paramslist)
               method prod = _const_prod
               val _const_params = paramslist |> (List.map s_to_id)
               method params = _const_params
             end)
      in
        `Peg
          (object
             val _const_postamble = postamble
             method postamble = _const_postamble
             val _const_preamble = preamble
             method preamble = _const_preamble
             val _const_exports =
               (list_of_entries |>
                  (List.map (fun (id, params, def) -> ((s_to_id id), id))))
                 |> alist_to_idmap
             method exports = _const_exports
             val _const_entries =
               alist_to_idmap
                 (List.map
                    (fun (id, params, def) ->
                       ((s_to_id id), (ntdef params def)))
                    list_of_entries)
             method entries = _const_entries
           end)
      
    let pegNoDefProds preamble list_of_entries postamble : pegGrammar =
      let internal = internal_nts list_of_entries in
      let ntdef params list_of_productions =
        let paramslist = params |> (Str.split (Str.regexp " +"))
        in
          `NonTermDef
            (object
               val _const_prod =
                 list_of_productions |> (fixnt internal paramslist)
               method prod = _const_prod
               val _const_params = paramslist |> (List.map s_to_id)
               method params = _const_params
             end)
      in
        `Peg
          (object
             val _const_postamble = postamble
             method postamble = _const_postamble
             val _const_preamble = preamble
             method preamble = _const_preamble
             val _const_exports =
               (list_of_entries |>
                  (List.map (fun (id, params, def) -> ((s_to_id id), id))))
                 |> alist_to_idmap
             method exports = _const_exports
             val _const_entries =
               alist_to_idmap
                 (List.map
                    (fun (id, params, def) ->
                       ((s_to_id id), (ntdef params def)))
                    list_of_entries)
             method entries = _const_entries
           end)
      
  end
  
let updateExternalMemocellsInfo l =
  needed_memocells_external :=
    List.fold_left
      (fun needed (s, what) -> IdentMap.add (PEGshort.s_to_id s) what needed)
      !needed_memocells_external l
  
(* (not so)pretty printer for PEG grammars
   meant primarily to be used to generate bootstrapping PEG grammar from Ocaml-coded PEG grammar *)
module PegPrint =
  struct
    let exprAST_to_string expr =
      let module ExportAst =
        struct
          open Lexing
            
          open Camlp4
            
          open PreCast
            
          open Camlp4.Sig
            
          module Ast2pt = Camlp4.Struct.Camlp4Ast2OCamlAst.Make(Ast)
            
          module Lexer = Camlp4.Struct.Lexer.Make(Token)
            
          module Printer = Camlp4.Printers.OCaml.Make(Camlp4.PreCast.Syntax)
            
          module Dumper =
            Camlp4.Printers.DumpOCamlAst.Make(Camlp4.PreCast.Syntax)
            
          let printer = (new Printer.printer ())#expr
            
        end
      in
        (ExportAst.printer Format.str_formatter expr;
         Format.flush_str_formatter ())
      
    let printer_ident oc =
      function | `Id id -> Printf.fprintf oc "%a" UString.print id#id
      
    let printer_ast oc expr =
      Printf.fprintf oc "<< %s >>" (exprAST_to_string expr)
      
    let printer_ast_dummy oc expr = ()
      
    let printer_params recc oc params =
      if not (List.is_empty params)
      then
        Printf.fprintf oc "%a"
          (List.print ~first: "(" ~last: ")" ~sep: ", " recc) params
      else ()
      
    let printer_paramdef oc params =
      if not (List.is_empty params)
      then
        Printf.fprintf oc "%a"
          (List.print ~first: "(" ~last: ")" ~sep: ", " printer_ident) params
      else ()
      
    let print_escaped oc us =
      Printf.fprintf oc "%a" UString.print (UString.escaped us)
      
    let printer_parsePrim_param ?(printFull = true) oc (p : parsePrim) =
      let open ParsePrim
      in
        let args =
          `MK
            (object
               val _const_fParam =
                 fun ~i ~name -> Printf.fprintf oc "%a" printer_ident name
               method fParam = _const_fParam
               val _const_fMemo =
                 fun ~recc ~p -> Printf.fprintf oc "(%a)^" (fun _ -> recc) p
               method fMemo = _const_fMemo
               val _const_fVoid = fun () -> Printf.fprintf oc "fail"
               method fVoid = _const_fVoid
               val _const_fEmpty = fun () -> ()
               method fEmpty = _const_fEmpty
               val _const_fExternal =
                 fun ~recc ~nonterm ~params ->
                   Printf.fprintf oc "%a%a" printer_ident nonterm
                     (printer_params (fun _ -> recc)) params
               method fExternal = _const_fExternal
               val _const_fNonterm =
                 fun ~recc ~nonterm ~params ->
                   Printf.fprintf oc "%a%a" printer_ident nonterm
                     (printer_params (fun _ -> recc)) params
               method fNonterm = _const_fNonterm
               val _const_fConcat =
                 fun ~recc ~p ~names ~action ->
                   (Printf.fprintf oc "(";
                    List.iter2
                      (fun p ->
                         function
                         | Some name when printFull ->
                             Printf.fprintf oc "%s:%a " name (fun _ -> recc)
                               p
                         | _ -> Printf.fprintf oc "%a " (fun _ -> recc) p)
                      p names;
                    Printf.fprintf oc "%a)"
                      (if printFull then printer_ast else printer_ast_dummy)
                      action)
               method fConcat = _const_fConcat
               val _const_fChoice =
                 fun ~recc ~p1 ~p2 ->
                   Printf.fprintf oc "(%a\n\t/ %a)" (fun _ -> recc) p1
                     (fun _ -> recc) p2
               method fChoice = _const_fChoice
               val _const_fOption =
                 fun ~recc ~p -> Printf.fprintf oc "?%a" (fun _ -> recc) p
               method fOption = _const_fOption
               val _const_fLookahead =
                 fun ~recc ~p -> Printf.fprintf oc "&%a" (fun _ -> recc) p
               method fLookahead = _const_fLookahead
               val _const_fNeg =
                 fun ~recc ~p -> Printf.fprintf oc "!%a" (fun _ -> recc) p
               method fNeg = _const_fNeg
               val _const_fString =
                 fun ~s -> Printf.fprintf oc "\"%a\"" print_escaped s
               method fString = _const_fString
               val _const_fTest =
                 fun ~recc ~p ~test ->
                   Printf.fprintf oc "&&( %a %a )" (fun _ -> recc) p
                     printer_ast test
               method fTest = _const_fTest
               val _const_fCharClass =
                 fun ~chars -> Printf.fprintf oc "[%a]" print_escaped chars
               method fCharClass = _const_fCharClass
               val _const_fAnyChar = fun () -> Printf.fprintf oc "."
               method fAnyChar = _const_fAnyChar
             end)
        in iter args p
      
    let printer_parsePrim oc p =
      printer_parsePrim_param ~printFull: true oc p
      
    let printer oc =
      function
      | (`Peg peg : pegGrammar) ->
          let print_def ntident =
            (function
             | `NonTermDef ntdef ->
                 Printf.fprintf oc "%a%a -> \n\t  %a;\n" printer_ident
                   ntident printer_paramdef ntdef#params printer_parsePrim
                   ntdef#prod)
          in IdentMap.iter print_def peg#entries
      
  end
  
module ParsePrimHashed =
  struct
    type t = parsePrim
    
    let equal (p1 : parsePrim) (p2 : parsePrim) =
      let _loc = Camlp4.PreCast.Loc.ghost
      in
        let open Camlp4.PreCast.Ast
        in
          let rec norm p = match p with | `Memo o -> norm o#p | _ -> p in
          let rec aux p1 p2 =
            match ((norm p1), (norm p2)) with
            | (`AnyChar _, `AnyChar _) -> true
            | (`CharClass o1, `CharClass o2) ->
                (UString.compare o1#chars o2#chars) == 0
            | (`Test o1, `Test o2) -> (aux o1#p o2#p) && (o1#test = o2#test)
            | (`String o1, `String o2) -> (UString.compare o1#s o2#s) == 0
            | (`Neg o1, `Neg o2) -> aux o1#p o2#p
            | (`Lookahead o1, `Lookahead o2) -> aux o1#p o2#p
            | (`Option o1, `Option o2) -> aux o1#p o2#p
            | (`Choice o1, `Choice o2) ->
                (aux o1#p1 o2#p1) && (aux o1#p2 o2#p2)
            | (`Concat o1, `Concat o2) -> List.for_all2 aux o1#p o2#p
            | (`Nonterm o1, `Nonterm o2) ->
                ((IdentOrdered.compare o1#nonterm o2#nonterm) == 0) &&
                  (List.for_all2 aux o1#params o2#params)
            | (`External o1, `External o2) ->
                ((IdentOrdered.compare o1#nonterm o2#nonterm) == 0) &&
                  (List.for_all2 aux o1#params o2#params)
            | (`Empty _, `Empty _) -> true
            | (`Void _, `Void _) -> true
            | (`Param o1, `Param o2) -> o1#i == o2#i
            | (_, _) -> false
          in aux p1 p2
      
    let hash p =
      let outstr = IO.output_string ()
      in
        (PegPrint.printer_parsePrim_param ~printFull: false outstr p;
         (IO.close_out outstr) |> Hashtbl.hash)
      
  end
  
(* Real code actually begins *)
module NontermTable =
  UniqueTable.Make
    (struct
       type t = ident
       
       let equal =
         function
         | `Id r1 ->
             (function | `Id r2 -> (UString.compare r1#id r2#id) == 0)
         
       let hash = function | `Id r -> r#id |> Hashtbl.hash
         
     end)
  
module ParsePrimTable = UniqueTable.Make(ParsePrimHashed)
  
module ParsePrimHashtbl = StdHashtbl.Make(ParsePrimHashed)
  
module ParsePrimHashSet = StdHashtbl.Make(ParsePrimHashed)
  
type parsePrimHashSet = unit ParsePrimHashSet.t

open Camlp4
  
open PreCast
  
let list_to_expr l =
  let _loc = Loc.ghost
  in
    List.fold_left
      (fun tl hd ->
         Ast.ExApp (_loc,
           (Ast.ExApp (_loc, (Ast.ExId (_loc, (Ast.IdUid (_loc, "::")))), hd)),
           tl))
      (Ast.ExId (_loc, (Ast.IdUid (_loc, "[]")))) l
  
let (recursive_decoupling :
     nonterminalDef identMap ->
       NontermTable.t -> (nonterminalDef identMap) list) =
  fun ntdefs nthash ->
    let module Node =
      struct
        open NontermTable
          
        type t = uobj
        
        let hash uobj = uobj.hcode
          
        let compare i1 i2 = Stdlib.compare i1.tag i2.tag
          
        let to_string uobj =
          let (`Id id) = uobj.obj in UString.to_string id#id
          
      end
    in let module G = Graph.Make(Node)
      in let open G
        in
          let (identToNode : ident -> Node.t) = NontermTable.uobj nthash in
          let (nodeToIdent : Node.t -> ident) =
            fun n -> let open NontermTable in n.obj in
          let nodes =
            ((IdentMap.keys ntdefs) |> (Enum.map identToNode)) |> List.
              of_enum in
          let (getDependencies : nonterminalDef -> NodeSet.t) =
            function
            | `NonTermDef o -> let open ParsePrim
                in
                  let deps =
                    fold
                      (`MK
                         (object
                            val _const_fParam = fold_default#fParam
                            method fParam = _const_fParam
                            val _const_fMemo = fold_default#fMemo
                            method fMemo = _const_fMemo
                            val _const_fVoid = fold_default#fVoid
                            method fVoid = _const_fVoid
                            val _const_fEmpty = fold_default#fEmpty
                            method fEmpty = _const_fEmpty
                            val _const_fExternal = fold_default#fExternal
                            method fExternal = _const_fExternal
                            val _const_fConcat = fold_default#fConcat
                            method fConcat = _const_fConcat
                            val _const_fChoice = fold_default#fChoice
                            method fChoice = _const_fChoice
                            val _const_fOption = fold_default#fOption
                            method fOption = _const_fOption
                            val _const_fLookahead = fold_default#fLookahead
                            method fLookahead = _const_fLookahead
                            val _const_fNeg = fold_default#fNeg
                            method fNeg = _const_fNeg
                            val _const_fString = fold_default#fString
                            method fString = _const_fString
                            val _const_fTest = fold_default#fTest
                            method fTest = _const_fTest
                            val _const_fCharClass = fold_default#fCharClass
                            method fCharClass = _const_fCharClass
                            val _const_fAnyChar = fold_default#fAnyChar
                            method fAnyChar = _const_fAnyChar
                            val _const_fNonterm =
                              fun deps ~recc ~nonterm ~params ->
                                List.fold_left recc
                                  (NodeSet.add (identToNode nonterm) deps)
                                  params
                            method fNonterm = _const_fNonterm
                          end))
                      NodeSet.empty o#prod
                  in deps in
          let ( *** ) f g (x, y) = ((f x), (g y)) in
          let dependencies : NodeSet.t NodeMap.t =
            (((IdentMap.bindings ntdefs) |>
                (List.map (identToNode *** getDependencies)))
               |> List.enum)
              |> NodeMap.of_enum in
          (*
  let _ =
    IdentMap.bindings ntdefs
      |> List.map (id *** getDependencies)
      |> Printf.printf "input deps\n%a\n" (List.print (Pair.print PegPrint.printer_ident G.printer_nodeset))
  in
*)
          let depgraph = reverse { nodes = nodes; edges = dependencies; } in
          let partitions = cyclic_topo_sort depgraph in
          let result =
            partitions |>
              (List.map
                 (fun nodes ->
                    NodeSet.fold
                      (fun node newntdefs ->
                         let ident = nodeToIdent node
                         in
                           IdentMap.add ident (IdentMap.find ident ntdefs)
                             newntdefs)
                      nodes IdentMap.empty))
          in result
  
let subst_params expr params = let open ParsePrim
  in
    map
      (`MK
         (object
            val _const_fMemo = map_default#fMemo
            method fMemo = _const_fMemo
            val _const_fVoid = map_default#fVoid
            method fVoid = _const_fVoid
            val _const_fEmpty = map_default#fEmpty
            method fEmpty = _const_fEmpty
            val _const_fExternal = map_default#fExternal
            method fExternal = _const_fExternal
            val _const_fNonterm = map_default#fNonterm
            method fNonterm = _const_fNonterm
            val _const_fConcat = map_default#fConcat
            method fConcat = _const_fConcat
            val _const_fChoice = map_default#fChoice
            method fChoice = _const_fChoice
            val _const_fOption = map_default#fOption
            method fOption = _const_fOption
            val _const_fLookahead = map_default#fLookahead
            method fLookahead = _const_fLookahead
            val _const_fNeg = map_default#fNeg
            method fNeg = _const_fNeg
            val _const_fString = map_default#fString
            method fString = _const_fString
            val _const_fTest = map_default#fTest
            method fTest = _const_fTest
            val _const_fCharClass = map_default#fCharClass
            method fCharClass = _const_fCharClass
            val _const_fAnyChar = map_default#fAnyChar
            method fAnyChar = _const_fAnyChar
            val _const_fParam = fun ~i ~name -> List.nth params i
            method fParam = _const_fParam
          end))
      expr
  
let has_param expr = let open ParsePrim
  in
    fold
      (`MK
         (object
            val _const_fMemo = fold_default#fMemo
            method fMemo = _const_fMemo
            val _const_fVoid = fold_default#fVoid
            method fVoid = _const_fVoid
            val _const_fEmpty = fold_default#fEmpty
            method fEmpty = _const_fEmpty
            val _const_fExternal = fold_default#fExternal
            method fExternal = _const_fExternal
            val _const_fNonterm = fold_default#fNonterm
            method fNonterm = _const_fNonterm
            val _const_fConcat = fold_default#fConcat
            method fConcat = _const_fConcat
            val _const_fChoice = fold_default#fChoice
            method fChoice = _const_fChoice
            val _const_fOption = fold_default#fOption
            method fOption = _const_fOption
            val _const_fLookahead = fold_default#fLookahead
            method fLookahead = _const_fLookahead
            val _const_fNeg = fold_default#fNeg
            method fNeg = _const_fNeg
            val _const_fString = fold_default#fString
            method fString = _const_fString
            val _const_fTest = fold_default#fTest
            method fTest = _const_fTest
            val _const_fCharClass = fold_default#fCharClass
            method fCharClass = _const_fCharClass
            val _const_fAnyChar = fold_default#fAnyChar
            method fAnyChar = _const_fAnyChar
            val _const_fParam = fun r ~i ~name -> true
            method fParam = _const_fParam
          end))
      false expr
  
let external_needed_cells nonterm params =
  let name =
    (match nonterm with | `Id o -> o | _ -> failwith "")#id |> UString.
      to_string in
  let _ =
    if not (IdentMap.mem nonterm !needed_memocells_external)
    then
      failwith (Printf.sprintf "Nonterminal %s has not been defined." name)
    else ()
  in
    ((IdentMap.find nonterm !needed_memocells_external) |> increasing) |>
      (List.map
         (fun i ->
            `External
              (object
                 val _const_nonterm =
                   (name ^ ("~memo" ^ (string_of_int i))) |> PEGshort.s_to_id
                 method nonterm = _const_nonterm
                 val _const_params = params
                 method params = _const_params
               end)))
  
let (calculate_needed_memocells :
     nonterminalDef identMap ->
       (((parsePrim list) identMap) * ((int ParsePrimHashtbl.t) identMap))) =
  fun ntdefs ->
    let emptyMap =
      IdentMap.fold
        (fun k _ map -> IdentMap.add k (ParsePrimHashSet.create 50) map)
        ntdefs IdentMap.empty in
    let prevNeeds = ref emptyMap in
    let prevChanged = ref false in
    let copyMap oldmap =
      IdentMap.fold
        (fun k v newmap -> IdentMap.add k (ParsePrimHashSet.copy v) newmap)
        oldmap IdentMap.empty in
    let (addNeed : parsePrimHashSet identMap -> ident -> parsePrim -> unit) =
      fun needs id pp ->
        let curset = IdentMap.find id needs
        in
          if not (ParsePrimHashSet.mem curset pp)
          then (ParsePrimHashSet.add curset pp (); prevChanged := true)
          else ()
    in
      (* step one: each module adds its direct needed memocells *)
      (* step two through N: each module adds the needed memocells of its dependencies *)
      (ntdefs |>
         (IdentMap.iter
            (fun k ->
               function
               | `NonTermDef o ->
                   o#prod |> (let open ParsePrim
                     in
                       iter
                         (`MK
                            (object
                               val _const_fParam = iter_default#fParam
                               method fParam = _const_fParam
                               val _const_fVoid = iter_default#fVoid
                               method fVoid = _const_fVoid
                               val _const_fEmpty = iter_default#fEmpty
                               method fEmpty = _const_fEmpty
                               val _const_fNonterm = iter_default#fNonterm
                               method fNonterm = _const_fNonterm
                               val _const_fConcat = iter_default#fConcat
                               method fConcat = _const_fConcat
                               val _const_fChoice = iter_default#fChoice
                               method fChoice = _const_fChoice
                               val _const_fOption = iter_default#fOption
                               method fOption = _const_fOption
                               val _const_fLookahead =
                                 iter_default#fLookahead
                               method fLookahead = _const_fLookahead
                               val _const_fNeg = iter_default#fNeg
                               method fNeg = _const_fNeg
                               val _const_fString = iter_default#fString
                               method fString = _const_fString
                               val _const_fTest = iter_default#fTest
                               method fTest = _const_fTest
                               val _const_fCharClass =
                                 iter_default#fCharClass
                               method fCharClass = _const_fCharClass
                               val _const_fAnyChar = iter_default#fAnyChar
                               method fAnyChar = _const_fAnyChar
                               val _const_fExternal =
                                 fun ~recc ~nonterm ~params ->
                                   (List.iter recc params;
                                    let _ =
                                      if
                                        not (IdentMap.mem nonterm !prevNeeds)
                                      then
                                        prevNeeds :=
                                          IdentMap.add nonterm
                                            (ParsePrimHashSet.create 50)
                                            !prevNeeds
                                      else () in
                                    let paramsId =
                                      (increasing (List.length params)) |>
                                        (List.map
                                           (fun i ->
                                              `Param
                                                (object
                                                   val _const_name =
                                                     ("_" ^ (string_of_int i))
                                                       |> PEGshort.s_to_id
                                                   method name = _const_name
                                                   val _const_i = i
                                                   method i = _const_i
                                                 end)))
                                    in
                                      (external_needed_cells nonterm paramsId)
                                        |>
                                        (List.iter
                                           (addNeed !prevNeeds nonterm)))
                               method fExternal = _const_fExternal
                               val _const_fMemo =
                                 fun ~recc ~p ->
                                   (recc p;
                                    if has_param p
                                    then addNeed !prevNeeds k p
                                    else ())
                               method fMemo = _const_fMemo
                             end)))));
       while !prevChanged do prevChanged := false;
         (let newNeeds = copyMap !prevNeeds
          in
            (IdentMap.iter
               (fun k ->
                  function
                  | `NonTermDef o ->
                      o#prod |> (let open ParsePrim
                        in
                          let addmore ~recc ~nonterm ~params =
                            (List.iter recc params;
                             if List.exists has_param params
                             then
                               (IdentMap.find nonterm !prevNeeds) |>
                                 (ParsePrimHashSet.iter
                                    (fun need _ ->
                                       let substNeed =
                                         subst_params need params
                                       in
                                         if has_param substNeed
                                         then addNeed newNeeds k substNeed
                                         else ()))
                             else ())
                          in
                            iter
                              (`MK
                                 (object
                                    val _const_fParam = iter_default#fParam
                                    method fParam = _const_fParam
                                    val _const_fMemo = iter_default#fMemo
                                    method fMemo = _const_fMemo
                                    val _const_fVoid = iter_default#fVoid
                                    method fVoid = _const_fVoid
                                    val _const_fEmpty = iter_default#fEmpty
                                    method fEmpty = _const_fEmpty
                                    val _const_fConcat = iter_default#fConcat
                                    method fConcat = _const_fConcat
                                    val _const_fChoice = iter_default#fChoice
                                    method fChoice = _const_fChoice
                                    val _const_fOption = iter_default#fOption
                                    method fOption = _const_fOption
                                    val _const_fLookahead =
                                      iter_default#fLookahead
                                    method fLookahead = _const_fLookahead
                                    val _const_fNeg = iter_default#fNeg
                                    method fNeg = _const_fNeg
                                    val _const_fString = iter_default#fString
                                    method fString = _const_fString
                                    val _const_fTest = iter_default#fTest
                                    method fTest = _const_fTest
                                    val _const_fCharClass =
                                      iter_default#fCharClass
                                    method fCharClass = _const_fCharClass
                                    val _const_fAnyChar =
                                      iter_default#fAnyChar
                                    method fAnyChar = _const_fAnyChar
                                    val _const_fExternal = addmore
                                    method fExternal = _const_fExternal
                                    val _const_fNonterm = addmore
                                    method fNonterm = _const_fNonterm
                                  end))))
               ntdefs;
             prevNeeds := newNeeds))
         done;
       let needsAsList =
         !prevNeeds |>
           (IdentMap.map
              (fun hash ->
                 ParsePrimHashSet.fold (fun k _ l -> k :: l) hash [])) in
       let needsAsHash =
         needsAsList |>
           (IdentMap.map
              (fun lst ->
                 let newhash = ParsePrimHashtbl.create 500
                 in
                   (ExtList.iteri
                      (fun i k -> ParsePrimHashtbl.add newhash k i) lst;
                    newhash)))
       in (needsAsList, needsAsHash))
  
(* actual parsing: generation *)
let (parseGen : pegGrammar -> Ast.str_item) =
  fun grammar ->
    let _loc = Loc.ghost in
    let nontermTable = NontermTable.create 500 in
    let parsePrimTable = ParsePrimTable.create 500 in
    let (`Peg peg) = grammar in
    let mutual_rec_blocks = recursive_decoupling peg#entries nontermTable in
    let (memo_needs_list, memo_needs_map) =
      calculate_needed_memocells peg#entries in
    (*
  let _ =
    IdentMap.bindings memo_needs_list |>
    List.map (fun (id, ps) -> Printf.printf "%a needs %a\n" PegPrint.printer_ident id (List.print PegPrint.printer_parsePrim) ps)
  in
*)
    let parse_func_name =
      function
      | `Id id ->
          "_parse_" ^
            (* ^ (ntid |> NontermTable.uniqueTag nontermTable |> string_of_int) ^ "_" *)
            (id#id |> UString.to_string) in
    let param_name i = "_param_" ^ (string_of_int i) in
    let memocell_of ntid (prim : parsePrim) =
      if has_param prim
      then
        (let i =
           ParsePrimHashtbl.find (IdentMap.find ntid memo_needs_map) prim in
         let stri = string_of_int i
         in
           Ast.ExApp (_loc,
             (Ast.ExApp (_loc,
                (Ast.ExId (_loc,
                   (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "List")),
                      (Ast.IdLid (_loc, "nth")))))),
                (Ast.ExId (_loc, (Ast.IdLid (_loc, "_memocells")))))),
             (Ast.ExInt (_loc, stri))))
      else
        (let i = ParsePrimTable.uniqueTag parsePrimTable prim in
         let stri = string_of_int i
         in
           Ast.ExApp (_loc,
             (Ast.ExApp (_loc,
                (Ast.ExId (_loc,
                   (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "Memotable")),
                      (Ast.IdLid (_loc, "get_memocell")))))),
                (Ast.ExAcc (_loc,
                   (Ast.ExId (_loc, (Ast.IdLid (_loc, "_memotable")))),
                   (Ast.ExId (_loc, (Ast.IdLid (_loc, "val")))))))),
             (Ast.ExInt (_loc, stri)))) in
    let rec genPrim (ntid : ident) (prim : parsePrim) =
      match prim with
      | `AnyChar o ->
          Ast.ExApp (_loc,
            (Ast.ExId (_loc,
               (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "UChannel")),
                  (Ast.IdLid (_loc, "get_one")))))),
            (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))
      | `CharClass o ->
          let chars = o#chars |> (ast_of_ustring _loc)
          in
            Ast.ExMat (_loc,
              (Ast.ExApp (_loc,
                 (Ast.ExId (_loc,
                    (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "UChannel")),
                       (Ast.IdLid (_loc, "get_one")))))),
                 (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))),
              (Ast.McOr (_loc,
                 (Ast.McArr (_loc,
                    (Ast.PaApp (_loc,
                       (Ast.PaApp (_loc,
                          (Ast.PaId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.PaId (_loc, (Ast.IdLid (_loc, "_head")))))),
                       (Ast.PaId (_loc, (Ast.IdLid (_loc, "_input")))))),
                    (Ast.ExApp (_loc,
                       (Ast.ExApp (_loc,
                          (Ast.ExId (_loc,
                             (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "UString")),
                                (Ast.IdLid (_loc, "contains")))))),
                          chars)),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_head")))))),
                    (Ast.ExApp (_loc,
                       (Ast.ExApp (_loc,
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.ExId (_loc, (Ast.IdLid (_loc, "_head")))))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))))),
                 (Ast.McArr (_loc, (Ast.PaAny _loc), (Ast.ExNil _loc),
                    (Ast.ExId (_loc, (Ast.IdUid (_loc, "None")))))))))
      | `Test o ->
          let pres = genPrim ntid o#p in
          let test = o#test
          in
            Ast.ExMat (_loc, pres,
              (Ast.McOr (_loc,
                 (Ast.McArr (_loc,
                    (Ast.PaApp (_loc,
                       (Ast.PaApp (_loc,
                          (Ast.PaId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.PaId (_loc, (Ast.IdLid (_loc, "_res")))))),
                       (Ast.PaAny _loc))),
                    (Ast.ExApp (_loc, test,
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_res")))))),
                    (Ast.ExApp (_loc,
                       (Ast.ExApp (_loc,
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "()")))))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))))),
                 (Ast.McArr (_loc, (Ast.PaAny _loc), (Ast.ExNil _loc),
                    (Ast.ExId (_loc, (Ast.IdUid (_loc, "None")))))))))
      | `String o ->
          let ps =
            (o#s |> UString.explode) |>
              (List.map
                 (fun c ->
                    `CharClass
                      (object
                         val _const_chars = UString.implode [ c ]
                         method chars = _const_chars
                       end))) in
          let names = List.map (fun _ -> None) ps in
          let action =
            let strng = o#s |> (ast_of_ustring _loc) in strng in
          let p' =
            `Concat
              (object
                 val _const_action = action
                 method action = _const_action
                 val _const_names = names
                 method names = _const_names
                 val _const_p = ps
                 method p = _const_p
               end)
          in genPrim ntid p'
      | `Neg o ->
          let pres = genPrim ntid o#p
          in
            Ast.ExMat (_loc, pres,
              (Ast.McOr (_loc,
                 (Ast.McArr (_loc,
                    (Ast.PaApp (_loc,
                       (Ast.PaId (_loc, (Ast.IdUid (_loc, "Some")))),
                       (Ast.PaAny _loc))),
                    (Ast.ExNil _loc),
                    (Ast.ExId (_loc, (Ast.IdUid (_loc, "None")))))),
                 (Ast.McArr (_loc,
                    (Ast.PaId (_loc, (Ast.IdUid (_loc, "None")))),
                    (Ast.ExNil _loc),
                    (Ast.ExApp (_loc,
                       (Ast.ExApp (_loc,
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "()")))))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))))))))
      | `Lookahead o ->
          let pres = genPrim ntid o#p
          in
            Ast.ExMat (_loc, pres,
              (Ast.McOr (_loc,
                 (Ast.McArr (_loc,
                    (Ast.PaApp (_loc,
                       (Ast.PaApp (_loc,
                          (Ast.PaId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.PaId (_loc, (Ast.IdLid (_loc, "_res")))))),
                       (Ast.PaAny _loc))),
                    (Ast.ExNil _loc),
                    (Ast.ExApp (_loc,
                       (Ast.ExApp (_loc,
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.ExId (_loc, (Ast.IdLid (_loc, "_res")))))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))))),
                 (Ast.McArr (_loc,
                    (Ast.PaId (_loc, (Ast.IdUid (_loc, "None")))),
                    (Ast.ExNil _loc),
                    (Ast.ExId (_loc, (Ast.IdUid (_loc, "None")))))))))
      | `Option o ->
          let pres = genPrim ntid o#p
          in
            Ast.ExMat (_loc, pres,
              (Ast.McOr (_loc,
                 (Ast.McArr (_loc,
                    (Ast.PaApp (_loc,
                       (Ast.PaApp (_loc,
                          (Ast.PaId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.PaId (_loc, (Ast.IdLid (_loc, "_res")))))),
                       (Ast.PaId (_loc, (Ast.IdLid (_loc, "_tail")))))),
                    (Ast.ExNil _loc),
                    (Ast.ExApp (_loc,
                       (Ast.ExApp (_loc,
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.ExApp (_loc,
                             (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                             (Ast.ExId (_loc, (Ast.IdLid (_loc, "_res")))))))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_tail")))))))),
                 (Ast.McArr (_loc,
                    (Ast.PaId (_loc, (Ast.IdUid (_loc, "None")))),
                    (Ast.ExNil _loc),
                    (Ast.ExApp (_loc,
                       (Ast.ExApp (_loc,
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "None")))))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))))))))
      | `Choice o ->
          let pres1 = genPrim ntid o#p1 in
          let pres2 = genPrim ntid o#p2
          in
            Ast.ExMat (_loc, pres1,
              (Ast.McOr (_loc,
                 (Ast.McArr (_loc,
                    (Ast.PaApp (_loc,
                       (Ast.PaId (_loc, (Ast.IdUid (_loc, "Some")))),
                       (Ast.PaId (_loc, (Ast.IdLid (_loc, "a")))))),
                    (Ast.ExNil _loc),
                    (Ast.ExApp (_loc,
                       (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "a")))))))),
                 (Ast.McArr (_loc,
                    (Ast.PaId (_loc, (Ast.IdUid (_loc, "None")))),
                    (Ast.ExNil _loc), pres2)))))
      | `Concat o ->
          let expr_with_hole =
            List.fold_left2
              (fun curexpr name p ->
                 let pres = genPrim ntid p in
                 let name = match name with | None -> "_" | Some s -> s
                 in
                   fun hole ->
                     curexpr
                       (Ast.ExMat (_loc, pres,
                          (Ast.McOr (_loc,
                             (Ast.McArr (_loc,
                                (Ast.PaApp (_loc,
                                   (Ast.PaApp (_loc,
                                      (Ast.PaId (_loc,
                                         (Ast.IdUid (_loc, "Some")))),
                                      (Ast.PaId (_loc,
                                         (Ast.IdLid (_loc, name)))))),
                                   (Ast.PaId (_loc,
                                      (Ast.IdLid (_loc, "_input")))))),
                                (Ast.ExNil _loc), hole)),
                             (Ast.McArr (_loc,
                                (Ast.PaId (_loc, (Ast.IdUid (_loc, "None")))),
                                (Ast.ExNil _loc),
                                (Ast.ExId (_loc, (Ast.IdUid (_loc, "None")))))))))))
              (fun hole -> hole) o#names o#p in
          let action = o#action
          in
            expr_with_hole
              (Ast.ExApp (_loc,
                 (Ast.ExApp (_loc,
                    (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))), action)),
                 (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input"))))))
      | `Nonterm o ->
          let memocells =
            ((IdentMap.find o#nonterm memo_needs_list) |>
               (List.map
                  (fun p -> memocell_of ntid (subst_params p o#params))))
              |> list_to_expr in
          let params head =
            o#params |>
              (List.fold_left
                 (fun head p ->
                    let body = genPrim ntid p
                    in
                      Ast.ExApp (_loc, head,
                        (Ast.ExFun (_loc,
                           (Ast.McArr (_loc,
                              (Ast.PaId (_loc,
                                 (Ast.IdLid (_loc, "_resetmemo")))),
                              (Ast.ExNil _loc),
                              (Ast.ExFun (_loc,
                                 (Ast.McArr (_loc,
                                    (Ast.PaId (_loc,
                                       (Ast.IdLid (_loc, "_input")))),
                                    (Ast.ExNil _loc), body))))))))))
                 head) in
          let fullparseexpr =
            let idmain = parse_func_name o#nonterm in
            let expr0 = Ast.ExId (_loc, (Ast.IdLid (_loc, idmain))) in
            let expr1 = params expr0
            in
              Ast.ExApp (_loc,
                (Ast.ExApp (_loc, (Ast.ExApp (_loc, expr1, memocells)),
                   (Ast.ExId (_loc, (Ast.IdUid (_loc, "False")))))),
                (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))
          in fullparseexpr
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
            ((external_needed_cells o#nonterm o#params) |>
               (List.map (memocell_of ntid)))
              |> list_to_expr in
          let params head =
            o#params |>
              (List.fold_left
                 (fun head p ->
                    let body = genPrim ntid p
                    in
                      Ast.ExApp (_loc, head,
                        (Ast.ExFun (_loc,
                           (Ast.McArr (_loc,
                              (Ast.PaId (_loc,
                                 (Ast.IdLid (_loc, "_resetmemo")))),
                              (Ast.ExNil _loc),
                              (Ast.ExFun (_loc,
                                 (Ast.McArr (_loc,
                                    (Ast.PaId (_loc,
                                       (Ast.IdLid (_loc, "_input")))),
                                    (Ast.ExNil _loc), body))))))))))
                 head) in
          let fullparseexpr =
            let idmain =
              "parse_" ^
                ((match o#nonterm with | `Id o -> o | _ -> failwith "")#id |>
                   UString.to_string) in
            let expr0 = Ast.ExId (_loc, (Ast.IdLid (_loc, idmain))) in
            let expr1 = params expr0
            in
              Ast.ExApp (_loc,
                (Ast.ExApp (_loc, (Ast.ExApp (_loc, expr1, memocells)),
                   (Ast.ExId (_loc, (Ast.IdUid (_loc, "True")))))),
                (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))
          in fullparseexpr
      | `Memo o ->
          let pres = genPrim ntid o#p in
          let memocell = memocell_of ntid o#p
          in
            Ast.ExLet (_loc, Ast.ReNil,
              (Ast.BiEq (_loc,
                 (Ast.PaId (_loc, (Ast.IdLid (_loc, "_memocell")))),
                 memocell)),
              (Ast.ExMat (_loc,
                 (Ast.ExApp (_loc,
                    (Ast.ExApp (_loc,
                       (Ast.ExId (_loc,
                          (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "Memotable")),
                             (Ast.IdLid (_loc, "find_in_memocell")))))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_memocell")))))),
                    (Ast.ExApp (_loc,
                       (Ast.ExId (_loc,
                          (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "UChannel")),
                             (Ast.IdLid (_loc, "offset")))))),
                       (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))))),
                 (Ast.McOr (_loc,
                    (Ast.McArr (_loc,
                       (Ast.PaId (_loc, (Ast.IdUid (_loc, "None")))),
                       (Ast.ExNil _loc),
                       (Ast.ExLet (_loc, Ast.ReNil,
                          (Ast.BiEq (_loc,
                             (Ast.PaId (_loc, (Ast.IdLid (_loc, "_res")))),
                             pres)),
                          (Ast.ExLet (_loc, Ast.ReNil,
                             (Ast.BiEq (_loc,
                                (Ast.PaId (_loc, (Ast.IdLid (_loc, "_res'")))),
                                (Ast.ExMat (_loc,
                                   (Ast.ExId (_loc,
                                      (Ast.IdLid (_loc, "_res")))),
                                   (Ast.McOr (_loc,
                                      (Ast.McArr (_loc,
                                         (Ast.PaApp (_loc,
                                            (Ast.PaApp (_loc,
                                               (Ast.PaId (_loc,
                                                  (Ast.IdUid (_loc, "Some")))),
                                               (Ast.PaId (_loc,
                                                  (Ast.IdLid (_loc,
                                                     "_actionres")))))),
                                            (Ast.PaId (_loc,
                                               (Ast.IdLid (_loc, "_input")))))),
                                         (Ast.ExNil _loc),
                                         (Ast.ExApp (_loc,
                                            (Ast.ExApp (_loc,
                                               (Ast.ExId (_loc,
                                                  (Ast.IdUid (_loc, "Some")))),
                                               (Ast.ExApp (_loc,
                                                  (Ast.ExId (_loc,
                                                     (Ast.IdAcc (_loc,
                                                        (Ast.IdUid (_loc,
                                                           "Obj")),
                                                        (Ast.IdLid (_loc,
                                                           "repr")))))),
                                                  (Ast.ExId (_loc,
                                                     (Ast.IdLid (_loc,
                                                        "_actionres")))))))),
                                            (Ast.ExId (_loc,
                                               (Ast.IdLid (_loc, "_input")))))))),
                                      (Ast.McArr (_loc,
                                         (Ast.PaId (_loc,
                                            (Ast.IdUid (_loc, "None")))),
                                         (Ast.ExNil _loc),
                                         (Ast.ExId (_loc,
                                            (Ast.IdUid (_loc, "None")))))))))))),
                             (Ast.ExSeq (_loc,
                                (Ast.ExSem (_loc,
                                   (Ast.ExApp (_loc,
                                      (Ast.ExApp (_loc,
                                         (Ast.ExApp (_loc,
                                            (Ast.ExId (_loc,
                                               (Ast.IdAcc (_loc,
                                                  (Ast.IdUid (_loc,
                                                     "Memotable")),
                                                  (Ast.IdLid (_loc,
                                                     "add_in_memocell")))))),
                                            (Ast.ExId (_loc,
                                               (Ast.IdLid (_loc, "_memocell")))))),
                                         (Ast.ExApp (_loc,
                                            (Ast.ExId (_loc,
                                               (Ast.IdAcc (_loc,
                                                  (Ast.IdUid (_loc,
                                                     "UChannel")),
                                                  (Ast.IdLid (_loc, "offset")))))),
                                            (Ast.ExId (_loc,
                                               (Ast.IdLid (_loc, "_input")))))))),
                                      (Ast.ExId (_loc,
                                         (Ast.IdLid (_loc, "_res'")))))),
                                   (Ast.ExId (_loc,
                                      (Ast.IdLid (_loc, "_res")))))))))))))),
                    (Ast.McOr (_loc,
                       (Ast.McArr (_loc,
                          (Ast.PaApp (_loc,
                             (Ast.PaId (_loc, (Ast.IdUid (_loc, "Some")))),
                             (Ast.PaApp (_loc,
                                (Ast.PaApp (_loc,
                                   (Ast.PaId (_loc,
                                      (Ast.IdUid (_loc, "Some")))),
                                   (Ast.PaId (_loc,
                                      (Ast.IdLid (_loc, "_res")))))),
                                (Ast.PaId (_loc,
                                   (Ast.IdLid (_loc, "_input")))))))),
                          (Ast.ExNil _loc),
                          (Ast.ExApp (_loc,
                             (Ast.ExApp (_loc,
                                (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
                                (Ast.ExApp (_loc,
                                   (Ast.ExId (_loc,
                                      (Ast.IdAcc (_loc,
                                         (Ast.IdUid (_loc, "Obj")),
                                         (Ast.IdLid (_loc, "obj")))))),
                                   (Ast.ExId (_loc,
                                      (Ast.IdLid (_loc, "_res")))))))),
                             (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))))),
                       (Ast.McArr (_loc,
                          (Ast.PaApp (_loc,
                             (Ast.PaId (_loc, (Ast.IdUid (_loc, "Some")))),
                             (Ast.PaId (_loc, (Ast.IdUid (_loc, "None")))))),
                          (Ast.ExNil _loc),
                          (Ast.ExId (_loc, (Ast.IdUid (_loc, "None")))))))))))))
      | `Param o ->
          let var = param_name o#i
          in
            Ast.ExApp (_loc,
              (Ast.ExApp (_loc, (Ast.ExId (_loc, (Ast.IdLid (_loc, var)))),
                 (Ast.ExId (_loc, (Ast.IdUid (_loc, "False")))))),
              (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))
      | `Empty _ ->
          Ast.ExApp (_loc,
            (Ast.ExApp (_loc, (Ast.ExId (_loc, (Ast.IdUid (_loc, "Some")))),
               (Ast.ExId (_loc, (Ast.IdUid (_loc, "()")))))),
            (Ast.ExId (_loc, (Ast.IdLid (_loc, "_input")))))
      | `Void _ -> Ast.ExId (_loc, (Ast.IdUid (_loc, "None"))) in
    let functions_for_mutual_rec_block ntdefs =
      let bindingAST =
        ((ntdefs |> IdentMap.bindings) |>
           (List.map
              (function
               | (ntname, `NonTermDef ntdef) ->
                   (ntname, (parse_func_name ntname),
                    (List.map (fun i -> param_name i)
                       ((ntdef#params |> List.length) |> increasing)),
                    (genPrim ntname ntdef#prod)))))
          |>
          (List.map
             (fun (name, funcname, funcparams, funcbody) ->
                let stateid =
                  (NontermTable.uniqueTag nontermTable name) |> string_of_int in
                let funcbody =
                  if
                    ((List.length funcparams) > 0) ||
                      (not _ALLOW_LEFT_RECURSION)
                  then
                    Ast.ExFun (_loc,
                      (Ast.McArr (_loc,
                         (Ast.PaId (_loc, (Ast.IdLid (_loc, "_memocells")))),
                         (Ast.ExNil _loc),
                         (Ast.ExFun (_loc,
                            (Ast.McArr (_loc,
                               (Ast.PaId (_loc,
                                  (Ast.IdLid (_loc, "_resetmemo")))),
                               (Ast.ExNil _loc),
                               (Ast.ExFun (_loc,
                                  (Ast.McArr (_loc,
                                     (Ast.PaId (_loc,
                                        (Ast.IdLid (_loc, "_input")))),
                                     (Ast.ExNil _loc),
                                     (Ast.ExSeq (_loc,
                                        (Ast.ExSem (_loc,
                                           (Ast.ExIfe (_loc,
                                              (Ast.ExId (_loc,
                                                 (Ast.IdLid (_loc,
                                                    "_resetmemo")))),
                                              (Ast.ExSeq (_loc,
                                                 (Ast.ExSem (_loc,
                                                    (Ast.ExAss (_loc,
                                                       (Ast.ExAcc (_loc,
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc,
                                                                "_memotable")))),
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc, "val")))))),
                                                       (Ast.ExApp (_loc,
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc,
                                                                "memotable_default")))),
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdUid
                                                                (_loc, "()")))))))),
                                                    (Ast.ExApp (_loc,
                                                       (Ast.ExId (_loc,
                                                          (Ast.IdAcc (_loc,
                                                             (Ast.IdUid
                                                                (_loc,
                                                                "LRHash")),
                                                             (Ast.IdLid
                                                                (_loc,
                                                                "clear")))))),
                                                       (Ast.ExId (_loc,
                                                          (Ast.IdLid (_loc,
                                                             "_lrinfo")))))))))),
                                              (Ast.ExId (_loc,
                                                 (Ast.IdUid (_loc, "()")))))),
                                           funcbody)))))))))))))))
                  else
                    Ast.ExFun (_loc,
                      (Ast.McArr (_loc,
                         (Ast.PaId (_loc, (Ast.IdLid (_loc, "_memocells")))),
                         (Ast.ExNil _loc),
                         (Ast.ExFun (_loc,
                            (Ast.McArr (_loc,
                               (Ast.PaId (_loc,
                                  (Ast.IdLid (_loc, "_resetmemo")))),
                               (Ast.ExNil _loc),
                               (Ast.ExFun (_loc,
                                  (Ast.McArr (_loc,
                                     (Ast.PaId (_loc,
                                        (Ast.IdLid (_loc, "_input")))),
                                     (Ast.ExNil _loc),
                                     (Ast.ExSeq (_loc,
                                        (Ast.ExSem (_loc,
                                           (Ast.ExIfe (_loc,
                                              (Ast.ExId (_loc,
                                                 (Ast.IdLid (_loc,
                                                    "_resetmemo")))),
                                              (Ast.ExSeq (_loc,
                                                 (Ast.ExSem (_loc,
                                                    (Ast.ExAss (_loc,
                                                       (Ast.ExAcc (_loc,
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc,
                                                                "_memotable")))),
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc, "val")))))),
                                                       (Ast.ExApp (_loc,
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc,
                                                                "memotable_default")))),
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdUid
                                                                (_loc, "()")))))))),
                                                    (Ast.ExApp (_loc,
                                                       (Ast.ExId (_loc,
                                                          (Ast.IdAcc (_loc,
                                                             (Ast.IdUid
                                                                (_loc,
                                                                "LRHash")),
                                                             (Ast.IdLid
                                                                (_loc,
                                                                "clear")))))),
                                                       (Ast.ExId (_loc,
                                                          (Ast.IdLid (_loc,
                                                             "_lrinfo")))))))))),
                                              (Ast.ExId (_loc,
                                                 (Ast.IdUid (_loc, "()")))))),
                                           (Ast.ExLet (_loc, Ast.ReNil,
                                              (Ast.BiEq (_loc,
                                                 (Ast.PaId (_loc,
                                                    (Ast.IdLid (_loc,
                                                       "_lrkey")))),
                                                 (Ast.ExTup (_loc,
                                                    (Ast.ExCom (_loc,
                                                       (Ast.ExInt (_loc,
                                                          stateid)),
                                                       (Ast.ExApp (_loc,
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdAcc
                                                                (_loc,
                                                                (Ast.IdUid
                                                                   (_loc,
                                                                   "UChannel")),
                                                                (Ast.IdLid
                                                                   (_loc,
                                                                   "offset")))))),
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc,
                                                                "_input")))))))))))),
                                              (Ast.ExIfe (_loc,
                                                 (Ast.ExApp (_loc,
                                                    (Ast.ExApp (_loc,
                                                       (Ast.ExId (_loc,
                                                          (Ast.IdAcc (_loc,
                                                             (Ast.IdUid
                                                                (_loc,
                                                                "LRHash")),
                                                             (Ast.IdLid
                                                                (_loc, "mem")))))),
                                                       (Ast.ExId (_loc,
                                                          (Ast.IdLid (_loc,
                                                             "_lrinfo")))))),
                                                    (Ast.ExId (_loc,
                                                       (Ast.IdLid (_loc,
                                                          "_lrkey")))))),
                                                 (Ast.ExLet (_loc, Ast.ReNil,
                                                    (Ast.BiEq (_loc,
                                                       (Ast.PaTup (_loc,
                                                          (Ast.PaCom (_loc,
                                                             (Ast.PaId (_loc,
                                                                (Ast.IdLid
                                                                   (_loc,
                                                                   "_used")))),
                                                             (Ast.PaId (_loc,
                                                                (Ast.IdLid
                                                                   (_loc,
                                                                   "_res")))))))),
                                                       (Ast.ExApp (_loc,
                                                          (Ast.ExApp (_loc,
                                                             (Ast.ExId (_loc,
                                                                (Ast.IdAcc
                                                                   (_loc,
                                                                   (Ast.IdUid
                                                                    (_loc,
                                                                    "LRHash")),
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "find")))))),
                                                             (Ast.ExId (_loc,
                                                                (Ast.IdLid
                                                                   (_loc,
                                                                   "_lrinfo")))))),
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc,
                                                                "_lrkey")))))))),
                                                    (Ast.ExSeq (_loc,
                                                       (Ast.ExSem (_loc,
                                                          (Ast.ExAss (_loc,
                                                             (Ast.ExAcc
                                                                (_loc,
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "_used")))),
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "val")))))),
                                                             (Ast.ExId (_loc,
                                                                (Ast.IdUid
                                                                   (_loc,
                                                                   "True")))))),
                                                          (Ast.ExApp (_loc,
                                                             (Ast.ExId (_loc,
                                                                (Ast.IdLid
                                                                   (_loc,
                                                                   "castLR")))),
                                                             (Ast.ExAcc
                                                                (_loc,
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "_res")))),
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "val")))))))))))))),
                                                 (Ast.ExLet (_loc, Ast.ReNil,
                                                    (Ast.BiEq (_loc,
                                                       (Ast.PaTup (_loc,
                                                          (Ast.PaCom (_loc,
                                                             (Ast.PaId (_loc,
                                                                (Ast.IdLid
                                                                   (_loc,
                                                                   "_used")))),
                                                             (Ast.PaId (_loc,
                                                                (Ast.IdLid
                                                                   (_loc,
                                                                   "_resPrev")))))))),
                                                       (Ast.ExTup (_loc,
                                                          (Ast.ExCom (_loc,
                                                             (Ast.ExApp
                                                                (_loc,
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "ref")))),
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdUid
                                                                    (_loc,
                                                                    "False")))))),
                                                             (Ast.ExApp
                                                                (_loc,
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "ref")))),
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdUid
                                                                    (_loc,
                                                                    "None")))))))))))),
                                                    (Ast.ExSeq (_loc,
                                                       (Ast.ExSem (_loc,
                                                          (Ast.ExApp (_loc,
                                                             (Ast.ExApp
                                                                (_loc,
                                                                (Ast.ExApp
                                                                   (_loc,
                                                                   (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdAcc
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdUid
                                                                    (_loc,
                                                                    "LRHash")),
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "add")))))),
                                                                   (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_lrinfo")))))),
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "_lrkey")))))),
                                                             (Ast.ExTup
                                                                (_loc,
                                                                (Ast.ExCom
                                                                   (_loc,
                                                                   (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_used")))),
                                                                   (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_resPrev")))))))))),
                                                          (Ast.ExLet (_loc,
                                                             Ast.ReNil,
                                                             (Ast.BiEq (_loc,
                                                                (Ast.PaId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "_res")))),
                                                                (Ast.ExApp
                                                                   (_loc,
                                                                   (Ast.ExApp
                                                                    (_loc,
                                                                    (Ast.
                                                                    ExApp
                                                                    (_loc,
                                                                    (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "growLR")))),
                                                                    (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_used")))))),
                                                                    (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_resPrev")))))),
                                                                   (Ast.ExFun
                                                                    (_loc,
                                                                    (Ast.
                                                                    McArr
                                                                    (_loc,
                                                                    (Ast.PaId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdUid
                                                                    (_loc,
                                                                    "()")))),
                                                                    (Ast.
                                                                    ExNil
                                                                    _loc),
                                                                    funcbody)))))))),
                                                             (Ast.ExSeq
                                                                (_loc,
                                                                (Ast.ExSem
                                                                   (_loc,
                                                                   (Ast.ExApp
                                                                    (_loc,
                                                                    (Ast.
                                                                    ExApp
                                                                    (_loc,
                                                                    (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdAcc
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdUid
                                                                    (_loc,
                                                                    "LRHash")),
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "remove")))))),
                                                                    (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_lrinfo")))))),
                                                                    (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_lrkey")))))),
                                                                   (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_res"))))))))))))))))))))))))))))))))))) in
                let funcbody =
                  if String.ends_with funcname "BM"
                  then
                    Ast.ExFun (_loc,
                      (Ast.McArr (_loc,
                         (Ast.PaId (_loc, (Ast.IdLid (_loc, "_memocells")))),
                         (Ast.ExNil _loc),
                         (Ast.ExFun (_loc,
                            (Ast.McArr (_loc,
                               (Ast.PaId (_loc,
                                  (Ast.IdLid (_loc, "_resetmemo")))),
                               (Ast.ExNil _loc),
                               (Ast.ExFun (_loc,
                                  (Ast.McArr (_loc,
                                     (Ast.PaId (_loc,
                                        (Ast.IdLid (_loc, "_input")))),
                                     (Ast.ExNil _loc),
                                     (Ast.ExApp (_loc,
                                        (Ast.ExApp (_loc,
                                           (Ast.ExId (_loc,
                                              (Ast.IdAcc (_loc,
                                                 (Ast.IdUid (_loc,
                                                    "Benchmark")),
                                                 (Ast.IdLid (_loc,
                                                    "cumulative")))))),
                                           (Ast.ExStr (_loc, funcname)))),
                                        (Ast.ExLaz (_loc,
                                           (Ast.ExApp (_loc,
                                              (Ast.ExApp (_loc,
                                                 (Ast.ExApp (_loc, funcbody,
                                                    (Ast.ExId (_loc,
                                                       (Ast.IdLid (_loc,
                                                          "_memocells")))))),
                                                 (Ast.ExId (_loc,
                                                    (Ast.IdLid (_loc,
                                                       "_resetmemo")))))),
                                              (Ast.ExId (_loc,
                                                 (Ast.IdLid (_loc, "_input")))))))))))))))))))))
                  else funcbody in
                let funcbody =
                  if _ADD_PROFILING_CODE
                  then
                    Ast.ExFun (_loc,
                      (Ast.McArr (_loc,
                         (Ast.PaId (_loc, (Ast.IdLid (_loc, "_memocells")))),
                         (Ast.ExNil _loc),
                         (Ast.ExFun (_loc,
                            (Ast.McArr (_loc,
                               (Ast.PaId (_loc,
                                  (Ast.IdLid (_loc, "_resetmemo")))),
                               (Ast.ExNil _loc),
                               (Ast.ExFun (_loc,
                                  (Ast.McArr (_loc,
                                     (Ast.PaId (_loc,
                                        (Ast.IdLid (_loc, "_input")))),
                                     (Ast.ExNil _loc),
                                     (Ast.ExSeq (_loc,
                                        (Ast.ExSem (_loc,
                                           (Ast.ExIfe (_loc,
                                              (Ast.ExAcc (_loc,
                                                 (Ast.ExId (_loc,
                                                    (Ast.IdLid (_loc,
                                                       "_profile")))),
                                                 (Ast.ExId (_loc,
                                                    (Ast.IdLid (_loc, "val")))))),
                                              (Ast.ExApp (_loc,
                                                 (Ast.ExId (_loc,
                                                    (Ast.IdLid (_loc,
                                                       "print_string")))),
                                                 (Ast.ExApp (_loc,
                                                    (Ast.ExApp (_loc,
                                                       (Ast.ExId (_loc,
                                                          (Ast.IdLid (_loc,
                                                             "^")))),
                                                       (Ast.ExStr (_loc,
                                                          "$$ ")))),
                                                    (Ast.ExApp (_loc,
                                                       (Ast.ExApp (_loc,
                                                          (Ast.ExId (_loc,
                                                             (Ast.IdLid
                                                                (_loc, "^")))),
                                                          (Ast.ExStr (_loc,
                                                             funcname)))),
                                                       (Ast.ExApp (_loc,
                                                          (Ast.ExApp (_loc,
                                                             (Ast.ExId (_loc,
                                                                (Ast.IdLid
                                                                   (_loc,
                                                                   "^")))),
                                                             (Ast.ExStr
                                                                (_loc, " ")))),
                                                          (Ast.ExApp (_loc,
                                                             (Ast.ExApp
                                                                (_loc,
                                                                (Ast.ExId
                                                                   (_loc,
                                                                   (Ast.IdLid
                                                                    (_loc,
                                                                    "^")))),
                                                                (Ast.ExApp
                                                                   (_loc,
                                                                   (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "string_of_int")))),
                                                                   (Ast.ExApp
                                                                    (_loc,
                                                                    (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdAcc
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdUid
                                                                    (_loc,
                                                                    "UChannel")),
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "offset")))))),
                                                                    (Ast.ExId
                                                                    (_loc,
                                                                    (Ast.
                                                                    IdLid
                                                                    (_loc,
                                                                    "_input")))))))))),
                                                             (Ast.ExStr
                                                                (_loc, "\\n")))))))))))),
                                              (Ast.ExId (_loc,
                                                 (Ast.IdUid (_loc, "()")))))),
                                           (Ast.ExApp (_loc,
                                              (Ast.ExApp (_loc,
                                                 (Ast.ExApp (_loc, funcbody,
                                                    (Ast.ExId (_loc,
                                                       (Ast.IdLid (_loc,
                                                          "_memocells")))))),
                                                 (Ast.ExId (_loc,
                                                    (Ast.IdLid (_loc,
                                                       "_resetmemo")))))),
                                              (Ast.ExId (_loc,
                                                 (Ast.IdLid (_loc, "_input")))))))))))))))))))))
                  else funcbody in
                let funcbody' =
                  List.fold_left
                    (fun expr param ->
                       Ast.ExFun (_loc,
                         (Ast.McArr (_loc,
                            (Ast.PaId (_loc, (Ast.IdLid (_loc, param)))),
                            (Ast.ExNil _loc), expr))))
                    funcbody (List.rev funcparams)
                in
                  Ast.BiEq (_loc,
                    (Ast.PaId (_loc, (Ast.IdLid (_loc, funcname)))),
                    funcbody'))) in
      let (bindingHD, bindingTL) =
        ((List.hd bindingAST), (List.tl bindingAST))
      in
        bindingTL |>
          (List.fold_left (fun cur elm -> Ast.BiAnd (_loc, cur, elm))
             bindingHD) in
    let all_functions =
      mutual_rec_blocks |>
        (List.fold_left
           (fun kexpr ntdefs rest ->
              let fs = functions_for_mutual_rec_block ntdefs
              in kexpr (Ast.ExLet (_loc, Ast.ReRecursive, fs, rest)))
           (fun rest -> rest)) in
    let (exportpat, exportbody) =
      let (exportnames, exportbodies) =
        (peg#exports |> IdentMap.bindings) |>
          (List.fold_left
             (fun (exportnames, exportbodies) (ntname, exportname) ->
                let funcname = parse_func_name ntname in
                let funcbodyBase =
                  Ast.ExId (_loc, (Ast.IdLid (_loc, funcname)))
                in
                  ((("parse_" ^ exportname) :: exportnames),
                   (funcbodyBase :: exportbodies)))
             ([], []))
      in
        List.fold_left2
          (fun (exportpat, exportbody) curname curbody ->
             ((Ast.PaTup (_loc,
                 (Ast.PaCom (_loc,
                    (Ast.PaId (_loc, (Ast.IdLid (_loc, curname)))),
                    exportpat)))),
              (Ast.ExTup (_loc, (Ast.ExCom (_loc, curbody, exportbody))))))
          ((Ast.PaAny _loc), (Ast.ExId (_loc, (Ast.IdUid (_loc, "()")))))
          exportnames exportbodies in
    let body = all_functions exportbody in
    let preamble =
      match peg#preamble with | Some s -> s | _ -> Ast.StNil _loc in
    let postamble =
      match peg#postamble with | Some s -> s | _ -> Ast.StNil _loc in
    let needed_external =
      ((peg#exports |> IdentMap.keys) |>
         (Enum.map
            (fun exportname ->
               let needed =
                 (IdentMap.find exportname memo_needs_list) |> List.length
               in
                 (((match exportname with | `Id o -> o | _ -> failwith "")#id
                     |> UString.to_string),
                  needed))))
        |> List.of_enum in
    let needed_external_ast =
      (needed_external |>
         (List.map
            (fun (a, b) ->
               let b = string_of_int b
               in
                 Ast.ExTup (_loc,
                   (Ast.ExCom (_loc, (Ast.ExStr (_loc, a)),
                      (Ast.ExInt (_loc, b))))))))
        |> list_to_expr
    in
      (updateExternalMemocellsInfo needed_external;
       Ast.StSem (_loc, preamble,
         (Ast.StSem (_loc,
            (Ast.StOpn (_loc, Ast.OvNil, (Ast.IdUid (_loc, "PegRuntime")))),
            (Ast.StSem (_loc,
               (Ast.StVal (_loc, Ast.ReNil,
                  (Ast.BiEq (_loc,
                     (Ast.PaId (_loc, (Ast.IdLid (_loc, "_memotable")))),
                     (Ast.ExTyc (_loc,
                        (Ast.ExApp (_loc,
                           (Ast.ExId (_loc, (Ast.IdLid (_loc, "ref")))),
                           (Ast.ExApp (_loc,
                              (Ast.ExId (_loc,
                                 (Ast.IdLid (_loc, "memotable_default")))),
                              (Ast.ExId (_loc, (Ast.IdUid (_loc, "()")))))))),
                        (Ast.TyApp (_loc,
                           (Ast.TyId (_loc, (Ast.IdLid (_loc, "ref")))),
                           (Ast.TyApp (_loc,
                              (Ast.TyId (_loc,
                                 (Ast.IdAcc (_loc,
                                    (Ast.IdUid (_loc, "Memotable")),
                                    (Ast.IdLid (_loc, "t")))))),
                              (Ast.TyApp (_loc,
                                 (Ast.TyId (_loc,
                                    (Ast.IdLid (_loc, "option")))),
                                 (Ast.TyTup (_loc,
                                    (Ast.TySta (_loc,
                                       (Ast.TyId (_loc,
                                          (Ast.IdAcc (_loc,
                                             (Ast.IdUid (_loc, "Obj")),
                                             (Ast.IdLid (_loc, "t")))))),
                                       (Ast.TyId (_loc,
                                          (Ast.IdAcc (_loc,
                                             (Ast.IdUid (_loc, "UChannel")),
                                             (Ast.IdLid (_loc, "t")))))))))))))))))))))),
               (Ast.StSem (_loc,
                  (Ast.StVal (_loc, Ast.ReNil,
                     (Ast.BiEq (_loc,
                        (Ast.PaId (_loc, (Ast.IdLid (_loc, "_lrinfo")))),
                        (Ast.ExApp (_loc,
                           (Ast.ExId (_loc,
                              (Ast.IdLid (_loc, "lrinfo_default")))),
                           (Ast.ExId (_loc, (Ast.IdUid (_loc, "()")))))))))),
                  (Ast.StSem (_loc,
                     (Ast.StVal (_loc, Ast.ReNil,
                        (Ast.BiEq (_loc,
                           (Ast.PaId (_loc, (Ast.IdLid (_loc, "_profile")))),
                           (Ast.ExApp (_loc,
                              (Ast.ExId (_loc, (Ast.IdLid (_loc, "ref")))),
                              (Ast.ExId (_loc, (Ast.IdUid (_loc, "False")))))))))),
                     (Ast.StSem (_loc,
                        (Ast.StVal (_loc, Ast.ReNil,
                           (Ast.BiEq (_loc, exportpat, body)))),
                        (Ast.StSem (_loc,
                           (Ast.StVal (_loc, Ast.ReNil,
                              (Ast.BiEq (_loc,
                                 (Ast.PaId (_loc, (Ast.IdUid (_loc, "()")))),
                                 (Ast.ExApp (_loc,
                                    (Ast.ExId (_loc,
                                       (Ast.IdAcc (_loc,
                                          (Ast.IdUid (_loc, "Peg")),
                                          (Ast.IdLid (_loc,
                                             "updateExternalMemocellsInfo")))))),
                                    needed_external_ast)))))),
                           postamble))))))))))))))
  
(* auxiliary definitions, to make the generated parsers easier to use *)
(* type of a parameterless generated parsing function yielding 'res *)
type 'res parser_t =
  ((((Obj.t * UChannel.t) option) PegRuntime.Memotable.memocell) ref) list ->
    bool -> UChannel.t -> ('res * UChannel.t) option

let peg_to_file s g = File.with_file_out s (fun oc -> PegPrint.printer oc g)
  
let string_of_peg g =
  let outstr = IO.output_string ()
  in (PegPrint.printer outstr g; IO.close_out outstr)
  
exception IncompleteParse of UChannel.t * UChannel.loc
  
let getFullParse result =
  match result with
  | Some (realresult, uc) ->
      (match UChannel.get_one uc with
       | Some _ ->
           raise
             (IncompleteParse (uc,
                (UChannel.loc uc)))
       | None -> realresult)
  | None -> failwith "failed to parse"
  
let parse_of_string ?initloc parsefunc s =
  ((UChannel.from_string ?initloc: initloc s) |> (parsefunc [] true)) |>
    getFullParse
  
let parse_of_file parsefunc s =
  ((UChannel.from_filename s) |> (parsefunc [] true)) |> getFullParse
  
let parse_of_uchannel parsefunc u = u |> (parsefunc [] true)
  
let option_parse_of_string parsefunc s =
  (UChannel.from_string s) |> (parsefunc [] true)
  


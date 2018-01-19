(*

The Makam metalanguage -- a tool for rapid language prototyping
Copyright (C) 2011- Antonis Stampoulis

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*)

open Batteries;;
open Utils;;
open StateEnvMonad;;

module Printf = struct
  include Printf ;;
  let sprintf = sprintf2 ;;
end;;

module IntOrdered = struct
  type t = int ;;
  let compare = Int.compare ;;
end ;;
module IMap = Map.Make(IntOrdered) ;;
module ISet = Set.Make(IntOrdered) ;;

module StringOrdered = struct
  type t = string ;;
  let compare = String.compare ;;
end;;
module Dict = Map.Make(StringOrdered) ;;
module StringSet = Set.Make(StringOrdered) ;;
module Path = BatPathGen.OfString;;

type ('a, 'b) typedterm = { term : 'a ; classifier : 'b ; loc : UChannel.span ; extra : Obj.t ref } ;;

type tindex =
  [ `Free | `Meta ] * int

type typP =
  [ `Arrow   of typ * typ
  | `TVar    of string * tindex option * typ list
  | `Forall  of (string * bool) list * typ
  | `TypeSort ]
and typ = (typP, unit) typedterm

type index =
    [ `Free | `Bound | `Meta ] * int

type name =
    [ `Concrete of string | `Abstract of string * int | `Anon ];;
type nameunifs = (name * name) list ;;

type exprP =
  [ `App of expr * expr
  | `Lam of name * typ * expr
  | `Var of name * index
  | `Const of Obj.t ]
and expr = (exprP, typ) typedterm ;;

type exprUP =
  [ `App of exprU * exprU
  | `Lam of name * typ * exprU
  | `Var of name * index option
  | `Const of Obj.t
  | `Annot of exprU * typ
  | `Unparsed of string ]
and exprU = (exprUP, typ) typedterm ;;

(* Free variables are constants; we allow type-based overloading and the free variable environment is mutable.
   Also, free variables should always have concrete types (no uninstantiated meta-variables).
   Bound variables work with shadowing. *)

let _DEBUG       = ref false ;;
let _DEBUG_TYPES = ref false ;;
let _DEBUG_NAMES = ref false ;;

type 'a located = { content : 'a ; span : UChannel.span } ;;

type ctxEnv = { name_to_bvar : (int list) Dict.t ;
                bvars        : int ;
                bvarnames    : string list ;
                typ_of_bvar  : typ IMap.t ;
                name_to_tpvar  : int Dict.t ;
                tpvars         : int ;
                tpvarnames     : string list ;
                term_focus     : [ `E of exprU | `T of typ | `None ] ;
                concrete_bound_names : bool ;
                resolve_ambiguous_vars : bool
              }
type ctxState = { name_to_fvar : (int list) Dict.t ;
                  fvar_to_name : string IMap.t ;
                  fvars        : int ;
                  typ_of_fvar  : typ IMap.t ;
                  name_to_meta : int Dict.t ;
                  meta_to_name : string IMap.t ;
                  metas        : int ;
                  typ_of_meta  : typ IMap.t ;
                  name_to_tfvar  : int Dict.t ;
                  tfvars         : int ;
                  arity_of_tfvar : int IMap.t ;
                  tmetas          : int ;
                  tmetanames      : string list ;
                  name_to_tmeta   : int Dict.t ;
                  tmeta_to_name   : string IMap.t ;
                  named_tmetas    : int ;
                  polytmetas      : int ;
                  tmeta_to_polytmeta : int IMap.t ;
                  parent_of_tmeta : typ IMap.t ;
                  treesize_of_tmeta : int IMap.t ;
                  tmeta_is_poly   : bool IMap.t;
                  current_module : string option ;
                  current_testsuite : string option ;
                  qualified_fvar_exists : StringSet.t ;
                  qualified_tfvar_exists : StringSet.t ;
                  globally_loaded_modules : StringSet.t ;
                  modules_loaded_in_modules : StringSet.t Dict.t ;
                  module_extension_stack : string option list ;
                  open_modules : string list ;
                  included_directories : string list ;
                  current_directory : string ;
                  cache_directory : string option ;
                  last_query : (unit -> exprU) located option
                } ;;

let empty_env () =
  { name_to_bvar  = Dict.empty ;  bvars = 0; bvarnames = [] ; typ_of_bvar  = IMap.empty ;
    name_to_tpvar = Dict.empty ; tpvars = 0 ; tpvarnames = [] ;
    term_focus = `None ; concrete_bound_names = false ; resolve_ambiguous_vars = true }
;;

let empty_state () =
  { name_to_fvar  = Dict.empty ; fvar_to_name = IMap.empty ; fvars = 0 ; typ_of_fvar  = IMap.empty ;
    name_to_meta  = Dict.empty ; metas = 0 ; typ_of_meta = IMap.empty ;
    meta_to_name  = IMap.empty ;
    name_to_tfvar = Dict.empty ; tfvars = 0 ; arity_of_tfvar = IMap.empty ;
    tmetas = 0 ; parent_of_tmeta = IMap.empty ; treesize_of_tmeta = IMap.empty ;
    tmeta_is_poly = IMap.empty ;
    tmetanames = [] ; name_to_tmeta = Dict.empty ;
    tmeta_to_name = IMap.empty ; named_tmetas = 0 ;
    polytmetas = 0 ; tmeta_to_polytmeta = IMap.empty ;
    current_module = None ; current_testsuite = None;
    qualified_fvar_exists = StringSet.empty ; qualified_tfvar_exists = StringSet.empty ;
    globally_loaded_modules = StringSet.empty ; modules_loaded_in_modules = Dict.empty ;
    cache_directory = None;
    module_extension_stack = [] ; open_modules = [] ; included_directories = [] ; current_directory = ".";
    last_query = None
  }
;;


(* optimization information modules *)
module DummyExtras = DeferredType.Make(struct
  type t = unit ;;
  let empty x = x ;;
  let uniquetag = 0 ;;
end) ;;

module ExprExtras = struct
  module Aux : DeferredType.Type = struct
    type t = unit ;;
    let empty () = () ;;
    let uniquetag = 1 ;;
  end ;;
  include DeferredType.Make(Aux) ;;
end ;;

module TypExtras = struct
  module Aux : DeferredType.Type = struct
    type t = unit ;;
    let empty () = () ;;
    let uniquetag = 2 ;;
  end ;;
  include DeferredType.Make(Aux) ;;
end ;;




(* string must be the first defined type, as we depend on it being there for name metas *)
let builtinStringType : typ ref = ref { term = `TVar("string", Some (`Free, 0), []) ; classifier = () ; loc = None ; extra = TypExtras.empty () } ;;
let dummyType = { term = `TypeSort ; classifier = () ; loc = None ; extra = TypExtras.empty () } ;;

module Const =
  struct

    module type ConstType = sig
      type t ;;
      val printer : t -> exprU -> string ;;
      val eq      : t -> t -> exprU -> exprU -> bool ;;
    end;;

    let builtin_types : (module ConstType) IMap.t ref = ref IMap.empty ;;

    let add_builtin_type i m =
      builtin_types := IMap.add i m !builtin_types
    ;;

    let string_of obj (expr : exprU) =
      match expr.classifier.term with
        `TVar(s, Some (`Free, idx), _) ->
          (try
             let module TypMod = (val IMap.find idx !builtin_types) in
             TypMod.printer (Obj.obj obj) expr
           with Not_found -> failwith ("TermLangCanon Error: Builtin type " ^ s ^ " not properly initialized.\n"))
      | _ -> failwith "TermLangCanon Error: Constant of unknown type.\n"
    ;;

    let eq o1 o2 e1 e2 =
      match e1.classifier.term with
        `TVar(s, Some(`Free, idx), _) ->
          (try
             let module TypMod = (val IMap.find idx !builtin_types) in
             TypMod.eq (Obj.obj o1) (Obj.obj o2) e1 e2
           with Not_found -> failwith ("TermLangCanon Error: Builtin type " ^ s ^ " not properly initialized.\n"))
      | _ -> failwith "TermLangCanon Error: Constant of unknown type.\n"
    ;;

  end;;


module Typ =
  struct
    let (print : 'a BatInnerIO.output -> typ -> unit) oc (typ : typ) =
      let indexprint oc idx =
        if !_DEBUG then
        match idx with
            Some (`Meta, i) -> Printf.fprintf oc "[t?%d]" i
          | Some (`Free, i) -> Printf.fprintf oc "[tf%d]" i
          | None            -> Printf.fprintf oc "[t??]"
        else
          Printf.fprintf oc ""
      in
      let printargs f oc args =
        if List.length args = 0 then Printf.fprintf oc ""
        else Printf.fprintf oc "%a" (List.print ~first:" " ~last:"" ~sep:" " f) args
      in
      let rec aux level oc (typ : typ) =
        let paren level' = if level < level' then "(", ")" else "", "" in
        match typ.term with
          `Arrow(t1,t2)   ->
            let oparen, cparen = paren 3 in
            Printf.fprintf oc "%s%a -> %a%s" oparen (aux 2) t1 (aux 3) t2 cparen
        | `TVar("", (Some (`Meta, i) as idx), args) ->
            let oparen, cparen = paren (if List.length args = 0 then 1 else 2) in
            let s = "_X" ^ (string_of_int i) in
            Printf.fprintf oc "%s%s%a%a%s" oparen s indexprint idx (printargs (aux 1)) args cparen
        | `TVar(s,i,args) ->
            let oparen, cparen = paren (if List.length args = 0 then 1 else 2) in
            (* TODO need a dequalify as well here for tfvars *)
            Printf.fprintf oc "%s%s%a%a%s" oparen s indexprint i (printargs (aux 1)) args cparen
        | `Forall(_,body) -> Printf.fprintf oc "%a" (aux level) body
        | `TypeSort       -> Printf.fprintf oc "type"
      in
      aux 3 oc typ
  end;;

let nameMetaPrefix = "ⁿ" ;;
let nameMetaSplit  = "ⁿⁿ" ;;
let toVarWithNamedMeta (s : string) (nmeta : string) : string = s ^ nameMetaSplit ^ nmeta ;;
let toNameMeta (s : string) : string = nameMetaPrefix ^ s ;;
let getNameMeta (s : string) : string =
  try snd (String.split s nameMetaSplit)
  with Not_found -> toNameMeta s
;;
let stripNameMeta (s : string) : string =
  try fst (String.split s nameMetaSplit)
  with Not_found -> s
 ;;
let isNameMeta (s : string) : bool = String.starts_with s nameMetaPrefix ;;
let hasNameMeta (s : string) : bool = try ignore(String.split s nameMetaSplit); true with Not_found -> false;;

let string_of_name (n : name) : string =
  match n with
    `Concrete(s) -> stripNameMeta s
  | `Abstract(s, _) -> s
  | `Anon -> "anon"
;;

let termstate = ref (empty_state ()) ;;
let termenv   = ref (empty_env   ()) ;;

(* TODO: this needs to take into account the presence of the same name in
   other prefixes *)
let dequalifyName (fully_qualified_name: string) =
  let state = !termstate in
  let possible_prefixes = state.current_module :: state.module_extension_stack in
  let result =
    List.fold_right (function None -> (fun res -> res) | Some prefix ->
        function | Some res -> Some res
                 | None ->
                    if (String.starts_with fully_qualified_name (prefix ^ "."))
                    then Some(String.lchop ~n:(1 + String.length prefix) fully_qualified_name)
                    else None) possible_prefixes None
  in
  Option.default fully_qualified_name result
;;

module ExprU =
  struct

    let rec gatherApp ?(args=[]) e =
      match e with
          { term = `App(e1,e2) } -> gatherApp e1 ~args:(e2 :: args)
        | _ -> e, args ;;

    let rec gatherLam ?(lams=[]) e =
      match e with
          { term = `Lam(s,t,e') } -> gatherLam e' ~lams:((s,t) :: lams)
        | _ -> e, List.rev lams ;;

    let user_string_of_name (qualified_names: bool) (n : name) : string =
      match n with
        `Concrete(s) ->
          let s' = stripNameMeta s in
          if qualified_names then s' else dequalifyName s'
      | `Abstract(s, _) -> s
      | `Anon -> "x"
    ;;

    let highlight : Obj.t = Obj.repr (ref ()) ;;

    let print_full ?(qualified_names=false) ?(debug=false) oc (expr : exprU) =
      let debug = debug || !_DEBUG in
      let binding oc (s, t) =
        let s = user_string_of_name qualified_names s in
        if debug then
          Printf.fprintf oc "(%s : %a)" s Typ.print t
        else
          Printf.fprintf oc "%s" s
      in
      let rec aux level oc expr =
        let openparen, closeparen = if level > 0 then "(", ")" else "", "" in
        let base oc expr =
        match expr with
            { term = `App( { term = `Const(o) }, e ) } when o == highlight ->
              let hlbegin = "\027[33m" in
              let hlend = "\027[0m" in
              Printf.fprintf oc "%s%a%s" hlbegin (aux level) e hlend

          | { term = `App _ } ->
              let e, args = gatherApp expr in
              Printf.fprintf oc "%s%a%s" openparen (List.print ~first:"" ~last:"" ~sep:" " (aux (level+1))) (e :: args) closeparen
          | { term = `Lam(_, _, _)  } ->
              let body, lams = gatherLam expr in
              Printf.fprintf oc "%s%s %a => %a%s" openparen "fun" (List.print ~first:"" ~last:"" ~sep:" " binding) lams (aux 0) body closeparen
          | { term = `Var(n,iv) } ->
              let s = user_string_of_name qualified_names n in
              if debug then
                (let realvar =
                   match iv with
                       Some(`Bound, i) -> "b"^(string_of_int i)
                     | Some(`Free, i)  -> "f"^(string_of_int i)
                     | Some(`Meta, i)  -> "?"^(string_of_int i)
                     | None            -> "??"
                 in
                Printf.fprintf oc "%s[%s]" s realvar)
              else
                Printf.fprintf oc "%s" s
          | { term = `Const(o); classifier = t } ->
              Printf.fprintf oc "%s" (Const.string_of o expr)
          | { term = `Annot(e, t) } ->
              Printf.fprintf oc "(%a : %a)" (aux 0) e Typ.print t
          | { term = `Unparsed(s) ; classifier = t } ->
              Printf.fprintf oc "{{ %s }}" s
        in

        if !_DEBUG_TYPES then
          Printf.fprintf oc "(%a : %a)" base expr Typ.print expr.classifier
        else
          base oc expr
      in
      aux 0 oc expr
    ;;

    let print ?(debug=false) oc expr =
      print_full ~qualified_names:false ~debug:debug oc expr
    ;;
  end

module Ctx =
  struct

    exception CurCtx of exn * (ctxEnv, ctxState) ctx ;;

    let choice (type a) ?(expectedException = fun _ -> true) (f : unit -> a) (g : unit -> a) : a =
      try f ()
      with e when expectedException e -> g ()
      | e -> raise e
    ;;

    let bench (type a) (s : string) (f : a Lazy.t) : a =
      Benchmark.cumulative s f
    ;;

    let inenv (type a) (env' : ctxEnv) (f : unit -> a) : a =

      let env = !termenv in
      termenv := env' ;
      let res = f () in
      termenv := env ;
      res

    ;;


  end;;


let exprAsExprU (e : expr) : exprU =
  let rec aux e =
    match e.term with
      `App(e1,e2)  -> { e with term = `App(aux e1, aux e2) }
    | `Lam(s,t,e') -> { e with term = `Lam(s,t,aux e') }
    | `Var(s,idx)  -> { e with term = `Var(s,Some idx) }
    | `Const(o)    -> { e with term = `Const(o) }
  in
  aux e
;;


exception UnifyError of typ * typ;;
exception OccursCheck of int * typ;;
exception WrongTermVar of exprU ;;
exception WrongTypeVar ;;
exception WrongTypeArity of int * int ;;
exception UnknownType of typ ;;
exception InvalidKind of typ ;;
exception AbstractionOverType of typ ;;
exception RankNPolymorphism of typ ;;
exception NoGenericParsingYet ;;


let newTMeta ?(isPoly = false) ?(name = "") loc : typ =

  let state = !termstate in
  let newmetaidx = state.tmetas in
  let newmeta = { term = `TVar(name, Some (`Meta, newmetaidx), []) ; classifier = () ; loc = loc ;
                  extra = TypExtras.empty () }
  in
  let state'  =
      if name = "" then
        { state with tmetas = state.tmetas + 1 ;
                     tmeta_is_poly   = IMap.add newmetaidx isPoly state.tmeta_is_poly }
      else
        { state with tmetas = state.tmetas + 1 ;
                     tmeta_is_poly   = IMap.add newmetaidx isPoly state.tmeta_is_poly ;
                     name_to_tmeta   = Dict.add name newmetaidx state.name_to_tmeta ;
                     tmetanames      = name :: state.tmetanames ;
                     named_tmetas    = state.named_tmetas + 1 ;
                     tmeta_to_name   = IMap.add newmetaidx name state.tmeta_to_name }
  in
  let state' = { state' with parent_of_tmeta = IMap.add newmetaidx newmeta state'.parent_of_tmeta ;
                             treesize_of_tmeta = IMap.add newmetaidx 1 state'.treesize_of_tmeta }
  in
  termstate := state' ;
  newmeta
;;


let clearMetas state =
  { state with metas = 0 ;
               typ_of_meta = IMap.empty ;
               meta_to_name = IMap.empty ;
               name_to_meta = Dict.empty ;
               (* type metas *)
               tmetas = 0;
               parent_of_tmeta = IMap.empty ;
               treesize_of_tmeta = IMap.empty ;
               tmeta_is_poly   = IMap.empty ;
               name_to_tmeta   = Dict.empty ;
               tmetanames      = [] ;
               named_tmetas    = 0 ;
               tmeta_to_name   = IMap.empty ;
               polytmetas      = 0 ;
               tmeta_to_polytmeta = IMap.empty }
;;

let clearMetasInState () = termstate := clearMetas !termstate ;;

let tmetaIsPoly (i : int) : bool = IMap.find i (!termstate).tmeta_is_poly ;;

let tmetaToPoly (i : int) : int =

  let state = !termstate in
  try IMap.find i state.tmeta_to_polytmeta
  with Not_found -> begin
    let idx = state.polytmetas in
    termstate := { state with tmeta_to_polytmeta = IMap.add i idx state.tmeta_to_polytmeta ;
                              polytmetas = state.polytmetas + 1 } ;
    idx
  end
;;


let setParent i t =
  let state = !termstate in
  termstate := { state with parent_of_tmeta = IMap.add i t state.parent_of_tmeta }
;;

let getParent i = IMap.find i (!termstate).parent_of_tmeta ;;

let setTreeSize i s =
  let state = !termstate in
  termstate := { state with treesize_of_tmeta = IMap.add i s state.treesize_of_tmeta }
;;

let getTreeSize i = IMap.find i (!termstate).treesize_of_tmeta ;;

let mergeParents i j ti tj =

  let szi = getTreeSize i in
  let szj = getTreeSize j in
  let newchild, newroot, newrootT, newsize =
    if szi < szj then i, j, tj, szj
    else if szj < szi then j, i, ti, szi
    else i, j, tj, szi + 1
  in
  setParent newchild newrootT ;
  setTreeSize newroot newsize
;;

let tmetaName (i : int) : string =

  let generateTMetaName i =
    let basename = (Char.code 'A') + (i mod 26) |> Char.chr |> String.of_char in
    basename ^ (if i / 26 > 0 then (string_of_int (i / 26)) else "")
  in

  let state = !termstate in
  try

    let name = IMap.find i state.tmeta_to_name in
    name

  with Not_found ->

    begin
      let name = generateTMetaName state.named_tmetas in
      termstate := { state with named_tmetas = state.named_tmetas + 1 ;
                                tmeta_to_name = IMap.add i name state.tmeta_to_name } ;
      name
    end
;;


let addTPoly name loc =
  let v = newTMeta ~isPoly:true ~name:name loc in
  match v.term with
  | `TVar(_, Some idx, _) -> idx
  | _ -> assert false
;;

let validTPolyName s =
  let us = s |> UString.of_string in
  (not (UString.is_empty us)) && (UString.gethd us |> UString.is_uppercase)
;;

let findTPoly name loc () =
  let state = !termstate in
  let idx =
    try (`Meta, Dict.find name state.name_to_tmeta) with
    | Not_found when validTPolyName name -> addTPoly name loc
    | Not_found -> raise (WrongTypeVar)
  in
  (name, idx, 0)
;;



let modify_module_dict m f d =
    try Dict.modify m f d
    with Not_found -> (failwith ("module " ^ m ^ " not found; this should not happen"))
;;

let addTFvar name arity =

  let state = !termstate in
  let idx = state.tfvars in
  let name, qualified_tfvar =
    match state.current_module with
        Some m -> (let name' = m ^ "." ^ name in
                   name', StringSet.add name' state.qualified_tfvar_exists)
      | None -> name, state.qualified_tfvar_exists
  in
  termstate := { state with tfvars = state.tfvars + 1 ;
                            name_to_tfvar = Dict.add name idx state.name_to_tfvar ;
                            qualified_tfvar_exists = qualified_tfvar ;
                            arity_of_tfvar = IMap.add idx arity state.arity_of_tfvar } ;
  idx
;;

let qualifyName qualset basedict n =

  let state = !termstate in
  if String.starts_with n "." then
    [String.tail n 1]
  else if state.current_module = None && state.open_modules = [] then
    [n]
  else begin
    let modules = state.current_module :: state.module_extension_stack ++ List.map Option.some state.open_modules in
    let fqnames = List.filter_map (function Some m -> Some (m ^ "." ^ n) | None -> None) modules in
    let basename = if Dict.mem n basedict then [n] else [] in
    let allnames =
      List.filter (fun x -> StringSet.mem x qualset) fqnames ++ basename
    in
    if List.length allnames = 0 then [n] else allnames
  end

;;

let findTFVar name () =

  let state = !termstate in
  let name' = qualifyName state.qualified_tfvar_exists state.name_to_tfvar name |> List.hd in
  let idx   =
    (try Dict.find name' state.name_to_tfvar
     with Not_found -> raise (WrongTypeVar))
  in
  let arity = IMap.find idx state.arity_of_tfvar in
  (name', (`Free, idx), arity)

;;

let checkArity arity arity' = if arity != arity' then raise (WrongTypeArity(arity, arity')) ;;

let addBvar s typ =
  let env = !termenv in
  let bvar = env.bvars in
  { env with bvars = env.bvars + 1;
             typ_of_bvar = IMap.add bvar typ env.typ_of_bvar ;
             bvarnames   = s :: env.bvarnames ;
             name_to_bvar = Dict.modify_def [] s (fun x -> bvar :: x) env.name_to_bvar }
;;

let findBvar s =

  let env = !termenv in
  try (let bvars = Dict.find s env.name_to_bvar in
       List.map (fun x -> env.bvars - 1 - x) bvars)
  with Not_found -> raise Not_found

;;

let addFvar s typ =

  let state = !termstate in
  let fvar = state.fvars in
  let s, qualified_fvar =
    match state.current_module with
        Some m -> (let s' = m ^ "." ^ s in
                   s', StringSet.add s' state.qualified_fvar_exists)
      | None -> s, state.qualified_fvar_exists
  in
  termstate := { state with fvars = state.fvars + 1 ;
                            name_to_fvar = Dict.modify_def [] s ((++)[fvar]) state.name_to_fvar ;
                            fvar_to_name = IMap.add fvar s state.fvar_to_name ;
                            typ_of_fvar  = IMap.add fvar typ state.typ_of_fvar ;
                            qualified_fvar_exists = qualified_fvar
               } ;
  fvar

;;

let findFvar s =

  let state = !termstate in
  let ss = qualifyName state.qualified_fvar_exists state.name_to_fvar s in
  try List.map (fun s -> Dict.find s state.name_to_fvar) ss |> List.flatten
  with Not_found -> raise Not_found

;;

let nameOfFVar i = IMap.find i (!termstate).fvar_to_name ;;

let lookupTIndex (varkind,i) =

  let state = !termstate in
  match varkind with

  | `Free ->

    (try IMap.find i state.arity_of_tfvar
     with Not_found -> raise WrongTypeVar)

  | `Meta -> if i < state.tmetas then 0 else raise WrongTypeVar

;;

let getResolveAmbiguousVars () = (!termenv).resolve_ambiguous_vars ;;

let setResolveAmbiguousVars t = { !termenv with resolve_ambiguous_vars = t } ;;

let findMeta loc ?(makeNameMeta = false) s =

  let state = !termstate in
  try  Dict.find s state.name_to_meta
  with Not_found ->
    if not (makeNameMeta || validTPolyName s || s ="_" || String.starts_with s "_") then
      raise (Not_found);
    let newmeta = state.metas in
    let tp      = if makeNameMeta then !(builtinStringType) else newTMeta loc in
    let state   = !termstate in
    termstate := { state with metas = state.metas + 1;
                              name_to_meta = (if s = "_" then state.name_to_meta
                                              else Dict.add s newmeta state.name_to_meta) ;
                              meta_to_name = IMap.add newmeta s state.meta_to_name ;
                              typ_of_meta  = IMap.add newmeta tp state.typ_of_meta } ;
    newmeta

;;

let substTPolys (t : typ) (tsubst : typ list) : typ =
  let rec aux t =
    let extra' = TypExtras.empty () in
    match t.term with
      `Arrow(t1,t2) -> { t with term = `Arrow(aux t1, aux t2) ; extra = extra' }
    | `TVar(_, Some (`Meta,idx), _) -> { t with term = (List.nth tsubst idx).term ; extra = extra'  }
    | `TVar(s, idx, args) -> { t with term = `TVar(s, idx, List.map aux args) ; extra = extra' }
    | _ -> assert false
  in
  aux t
;;

let instantiateWithTPolys loc (t : typ) =

  match t.term with

    `Forall(quant, body) ->

      let tsubst = List.map (fun n -> newTMeta ~isPoly:true ~name:"" loc) quant in
      substTPolys body tsubst

  | _ -> t

;;

let instantiateWithTFvars (t : typ) =

  match t.term with

    `Forall(quant, body) ->

      let tsubst = List.map (fun (name, parametric) ->

          if parametric then begin

            let i = addTFvar name 0 in
            { term = `TVar(name, Some (`Free, i), []) ; classifier = () ; loc = UChannel.span_end t.loc ;
              extra = TypExtras.empty () }

          end

          else newTMeta ~isPoly:true ~name:"" (UChannel.span_end t.loc))

        quant
      in
      substTPolys body tsubst

    | _ -> t
;;


let lookupIndex (varkind,i) loc =

  let state = !termstate in
  let env   = !termenv in
  let result = begin
      match varkind with
          `Bound -> IMap.find (env.bvars - i - 1) env.typ_of_bvar
        | `Free ->  let polytyp = IMap.find i state.typ_of_fvar in
                    instantiateWithTPolys (UChannel.span_end loc) polytyp
        | `Meta -> IMap.find i state.typ_of_meta
  end in
  result

;;

let lookupFVarPolytyp i = IMap.find i (!termstate).typ_of_fvar ;;


let getExprFocus () =

  match (!termenv).term_focus with
    | `E focus -> focus
    | _ -> { term = `Const(Obj.repr "[unknown]") ; classifier = !builtinStringType ;
             loc = None ; extra = ExprExtras.empty () }

;;

let getTypeFocus () =

  match (!termenv).term_focus with
    | `T focus -> focus
    | _ -> { term = `TVar("[unknown]", None, []) ; classifier = () ;
             loc = None ; extra = TypExtras.empty () }

;;

let getFocus () = (!termenv).term_focus ;;

let setFocus t = { !termenv with term_focus = t } ;;

let getConcreteBoundMode () = (!termenv).concrete_bound_names ;;

let withConcreteBoundMode mode f =
  let env' = { !termenv with concrete_bound_names = mode } in
  Ctx.inenv env' f
;;

let traverseType ?(uninstantiatedMeta = fun (t : typ) -> t)
                 ?(instantiatedMeta   = fun chase (t : typ) -> chase t)
                 ?(var                = fun chase (t : typ) -> t)
                 ?(arrow              = fun chase (t : typ) -> t)
                 (t : typ) =

  let rec chase t =
  match t.term with

  | `TVar(_, Some (`Meta, i), _) ->

    let parent = getParent i in
    (match parent.term with

      `TVar(_, Some (`Meta, j), _) when i == j -> uninstantiatedMeta t

    | `TVar(_, Some (`Meta, j), _) ->

      let grandparent = getParent j in
      setParent i grandparent ;
      chase parent

    | _ -> instantiatedMeta chase parent)

  | `TVar(name, idx, args) -> var chase t

  | `Arrow(t1,t2) -> arrow chase t

  | `TypeSort -> t

  | `Forall(_,_) -> assert false

  in

  chase t
;;

(* much cheaper than using traverseType ;
   traverseType does a lot of unnecessary allocations and does deep
   inspection also; the reason is the use of parameters like var and arrow --
   they are the identity but the compiler isn't optimizing it properly *)
let chaseType t =
  let rec aux t =
    match t.term with
    | `TVar(_, Some (`Meta, i), _) ->
      (match IMap.find i (!termstate).parent_of_tmeta with
        { term = `TVar(_, Some (`Meta, j), _) } when j == i -> t
      | t' -> aux t')
    | _ -> t
  in
  aux t
;;


let traverseTypeDeep
    ?(uninstantiatedMeta = fun t -> t) (t : typ) =

  traverseType t

    ~uninstantiatedMeta:uninstantiatedMeta

    ~var:(fun chase -> fun t -> match t.term with

        `TVar(name, idx, args) ->

          let args' = List.map chase args in
          { t with term = `TVar(name, idx, args') ; extra = TypExtras.empty () }

    | _ -> assert false)

    ~arrow:(fun chase -> fun t -> match t.term with

        `Arrow(t1, t2) ->

          let t1', t2' = chase t1, chase t2 in
          { t with term = `Arrow(t1', t2') ; extra = TypExtras.empty () }

    | _ -> assert false)
;;

let chaseTypeDeep ?(metasAreFine=false) ?(replaceUninst=false) t () =
  Ctx.bench "chase type deep" (lazy(
  traverseTypeDeep t
               ~uninstantiatedMeta:(fun t' ->
                 match t'.term with
                 `TVar(name, Some (`Meta, i), args) ->

                     if metasAreFine || tmetaIsPoly i then (
                       if replaceUninst then
                         { t' with term = `TVar(name, Some (`Meta, tmetaToPoly i), args) }
                       else t')
                     else raise (UnknownType(t))
                 | _ -> assert false
               )))
;;

let prepareTypeForUser t =

  traverseTypeDeep t
               ~uninstantiatedMeta:(fun t' -> match t'.term with
                 `TVar(_, Some (`Meta, i), args) ->
                   let name = tmetaName i in
                   { t' with term = `TVar(name, Some (`Meta, i), args) }
                 | _ -> assert false)

;;

let occursCheck i (t : typ) =
  let rec aux tfocus =

    match tfocus.term with

      `TVar(_, Some (`Meta, j), _) when j == i -> raise (OccursCheck(i,t))

    | `TVar(_, _, args) -> List.iter aux (List.map chaseType args)

    | `Arrow(t1,t2) -> List.iter aux (List.map chaseType [ t1 ; t2 ])

    | _ -> assert false

  in
  aux t

;;


let chasedTypUnify (t1 : typ) (t2 : typ) : unit =

  match t1.term, t2.term with

      `TVar(_, Some (`Meta, i), _), `TVar(_, Some (`Meta, j), _) when i == j -> ()

    | `TVar(_, Some (`Meta, i), _), `TVar(_, Some (`Meta, j), _) ->

      let isPoly1 = tmetaIsPoly i in
      let isPoly2 = tmetaIsPoly j in
      if isPoly1 then setParent j t1
      else if isPoly2 then setParent i t2
      else mergeParents i j t1 t2

    | `TVar(_, Some (`Meta, i), _), _ ->

      occursCheck i t2 ;
      setParent i t2

    | _, _ -> assert false

;;


let typUnify ?(allow_instantiation = true) t1top t2top =

  let rec typUnify t1 t2 =

    let t1 = chaseType t1 in
    let t2 = chaseType t2 in

    match t1.term, t2.term with

        `Arrow(t1d,t1r), `Arrow(t2d,t2r) ->

          typUnify t1d t2d ;
          typUnify t1r t2r

      | `TVar(_, Some idx1, args1), `TVar(_, Some idx2, args2) when idx1 = idx2 ->

        List.iter2 typUnify args1 args2

      | `TVar(_, Some (`Meta, i), _), _ when allow_instantiation -> chasedTypUnify t1 t2

      | _, `TVar(_, Some (`Meta, i), _) when allow_instantiation -> chasedTypUnify t2 t1

      | `TVar(_, (Some (`Meta, i)), _), `TVar(_, (Some (`Meta, j)), _)
          when not allow_instantiation && i == j -> ()

      | _ -> raise (UnifyError (t1top,t2top))
  in
  (* Ctx.bench "type unification" (lazy(typUnify t1top t2top)) *)
  typUnify t1top t2top
;;


let chaseTypesInExpr ?(metasAreFine = false) ?(replaceUninst = false) (e : expr) =

  let rec chaseTypesInExpr e =

    let env = setFocus (`E (exprAsExprU e)) in
    let t   = Ctx.inenv env (chaseTypeDeep ~metasAreFine:metasAreFine ~replaceUninst:replaceUninst e.classifier) in
    let e   = { e with classifier = t } in
    match e.term with

    | `App(e1, e2) ->

        let e1 = chaseTypesInExpr e1 in
        let e2 = chaseTypesInExpr e2 in
        { e with term = `App(e1,e2) }

    | `Lam(s, t', e') ->

      let t' = Ctx.inenv env (chaseTypeDeep ~metasAreFine:metasAreFine ~replaceUninst:replaceUninst t') in
      let e' = chaseTypesInExpr e' in
      { e with term = `Lam(s, t', e') }


    | _ -> { e with classifier = t }

  in

  chaseTypesInExpr e

;;


let rec findUnifiableVar kind (vars : int list) ({ classifier = tRes } as eFull) =

  let unifvars =

    match vars with
    | [] -> raise (WrongTermVar(eFull))
    | i :: [] -> [ i ]
    | _ when not(getResolveAmbiguousVars()) -> raise (WrongTermVar(eFull))
    | _ ->
      (let unifiable = List.map (fun v -> let state = !termstate in
                                          let typ = lookupIndex (kind, v) eFull.loc in
                                          let (//) = Ctx.choice
                                            ~expectedException:begin
                                              function
                                              | UnifyError(_,_) | OccursCheck(_,_) -> true
                                              | _ -> false
                                            end
                                          in
                                          let b = (fun _ -> typUnify typ tRes; true) //
                                                  (fun _ -> false)
                                          in
                                          termstate := state ;
                                          b) vars
       in
       let unifvars = List.combine vars unifiable |> List.filter snd |> List.map fst in
       unifvars)

  in
  let returnResult i =
    let index = kind, i in
    let typ = lookupIndex index eFull.loc in
    typUnify typ tRes ;
    index
  in
  match unifvars, eFull with
  | [], _ -> raise (WrongTermVar(eFull))
  (* This is a hack so that normal lists are the default when we overload nil/cons.
     TODO: find a better way to do this *)
  | l, { term = `Var (`Concrete(s), _) } when List.mem s [ "nil"; "cons" ] ->
     returnResult (List.last l)
  | i::_, _ -> returnResult i

;;

let fixBinder (n : name) : name =

  match n with
    `Concrete(s) -> `Concrete(stripNameMeta s)
  | _ -> n

;;

let fixAbstractBinder (n : name) : name =

  let concreteMode = getConcreteBoundMode () in
  match n with

  | `Concrete(s) when not concreteMode || hasNameMeta s ->

    let s' = stripNameMeta s in
    let nmeta = findMeta None ~makeNameMeta:true (getNameMeta s) in
    `Abstract(s', nmeta)

  | _ -> fixBinder n

;;

let fixAbstractName (n : name) (i : index) : name =

  match i with
    `Bound, _ -> fixAbstractBinder n

  | `Free, idx ->
    (match n with
      `Concrete(_) -> `Concrete(nameOfFVar idx)
    | _ -> n)

  | _ -> fixBinder n

;;

let namesForAnonVars (e : expr) : expr =

  let fixName n =
    match n with
        `Anon -> let state = !termstate in
                 let i = state.metas in
                 let s = "anon" ^ (string_of_int i) in
                 let nmeta = findMeta None ~makeNameMeta:true (getNameMeta s) in
                 `Abstract(s, nmeta)
      | _ -> n
  in

  let rec aux names e =

    match e.term with
        `App(e1, e2) -> let e1' = aux names e1 in
                        let e2' = aux names e2 in
                        { e with term = `App(e1', e2') }

      | `Lam(n,t,e') -> let n' = fixName n in
                        let e' = aux (n'::names) e' in
                        { e with term = `Lam(n',t,e') }

      | `Var(`Anon,(`Bound,i)) -> { e with term = `Var(List.nth names i, (`Bound, i)) }

      | _ -> e

  in

  aux [] e

;;




(*
type expr_parser = string -> string -> UChannel.loc -> exprU Ctx.Monad.m ;;
let default_expr_parser  : expr_parser ref = ref (fun t _ loc -> failwith (Printf.sprintf "No parser for type %s at %s." t (UChannel.string_of_loc loc))) ;;
let table_of_expr_parser : expr_parser IMap.t ref = ref IMap.empty ;;
let reset_expr_parsers () = table_of_expr_parser := IMap.empty ;;
let (add_expr_parser : typ -> expr_parser -> unit) t ep = table_of_expr_parser := TypMap.add t ep !table_of_expr_parser ;;
let (get_expr_parser : typ -> expr_parser) t = match TypMap.Exceptionless.find t !table_of_expr_parser with Some ep -> ep | None -> !default_expr_parser ;;
*)


(* --------------
   Type checking.
   -------------- *)

let gatherArrows t =
  let rec aux acc t =
    match (chaseType t).term with
      `Arrow(t1, t2) -> aux (t::acc) t2
    | _  -> List.rev acc, t
  in
  aux [] t
;;

let gatherArrowTyps t =
  let rec aux acc t =
    match (chaseType t).term with
      `Arrow(t1, t2) -> aux (t1::acc) t2
    | _  -> List.rev acc
  in
  aux [] t
;;

let isTypeSort t =
  match t.term with
    `TypeSort -> true
  | `TVar(s, None, []) when s = "type" -> true
  | _ -> false
;;

(* kindcheck_typeconstr:  |- κ wf   ( κ = type^n -> type ). returns the arity n. *)
let rec kindcheck_typeconstr ( { term = t } as tFull : typ ) : int  =

  match t with
    `TypeSort -> 0
  | `Arrow({ term = `TypeSort }, t2) -> 1 + (kindcheck_typeconstr t2)
  | _ -> raise (InvalidKind tFull)

;;

(* kindcheck_type: Δ |- τ : type  ( τ = τ1 -> τ2,
                                    τ = α (τ^n) where (a : type^n -> type) ) *)
let kindcheck_type (t : typ) : typ =

  let rec aux t =

    let env = setFocus (`T t) in
    Ctx.inenv env begin fun _ ->
    match t.term with

    | `Arrow(t1, t2) ->

      let t1' = aux t1 in
      let t2' = aux t2 in
      { t with term = `Arrow(t1', t2') }

    | `TVar(s, None, args) ->

       let (//) = Ctx.choice ~expectedException:(function WrongTypeVar -> true | _ -> false) in
       let (s', idx, arity)  = ( findTFVar s ) // ( findTPoly s t.loc ) in
       let _                 = checkArity arity (List.length args) in
       let args'             = List.map aux args in
       { t with term = `TVar(s', Some idx, args') }

    | `TVar(s, Some idx, args) ->

      let arity = lookupTIndex idx in
      let _     = checkArity arity (List.length args) in
      let args' = List.map aux args in
      { t with term = `TVar(s, Some idx, args') }

    | `TypeSort -> raise (AbstractionOverType(t))

    | `Forall _ -> raise (RankNPolymorphism(t))

    end

  in

  aux t

;;

(* let kindcheck_type t = Ctx.bench "kind checking" (lazy(kindcheck_type t)) ;; *)

let quantifyOverTPolys adhocnames (t : typ) : typ =

  let adhocnames = List.enum adhocnames |> StringSet.of_enum in
  let state = !termstate in
  if state.tmetas = 0
  then t
  else (let names = List.rev state.tmetanames in
        let parametric = List.map (fun x -> not(StringSet.mem x adhocnames)) names in
        let binders = List.combine names parametric in
        { term = `Forall(binders, t) ; classifier = () ; loc = t.loc ; extra = TypExtras.empty () })
;;

let type_declaration (s : string) (t : typ) : int =

  let _, tbody = gatherArrows t in

  match tbody.term with
    `TypeSort -> let arity = kindcheck_typeconstr t in
                 let i     = addTFvar s arity in
                 i

  | _ -> let adhoclist, t =
           match t.term with `Forall(binders, t) -> List.filter (fun (_, isParam) -> not isParam) binders, t | _ -> [], t
         in
         let adhocnames = List.map fst adhoclist in
         let t' = kindcheck_type t in
         let t' = quantifyOverTPolys adhocnames t' in
         let i  = addFvar s t' in
         i

;;


(* Abbreviations for types. *)
let _tType =
  { term = `TypeSort ; classifier = () ; loc = None ; extra = TypExtras.empty () };;
let _tVar ?(loc = None) ?(args = []) x =
  { term = `TVar(x, None, args) ; classifier = () ; loc = loc ; extra = TypExtras.empty () };;
let _tArrow ?(loc = None) t1 t2 =
  { term = `Arrow(t1,t2) ; classifier = () ; loc = loc ; extra = TypExtras.empty () } ;;
let _tForallAdhoc ?(loc = None) names t =
  { term = `Forall(List.map (fun x -> x, false) names, t); classifier = () ; loc = loc ; extra = TypExtras.empty () } ;;
let _tForallParam ?(loc = None) names t =
  { term = `Forall(List.map (fun x -> x, true) names, t); classifier = () ; loc = loc ; extra = TypExtras.empty () } ;;

let ( ~*  ) ?(loc = None) x     = _tVar ~loc:loc ~args:[] x ;;
let ( **> ) ?(loc = None) t1 t2 = _tArrow ~loc:loc t1 t2 ;;

(* Type checking for expressions. *)

let kindcheck_expr (e : exprU) : exprU =

  let t = kindcheck_type e.classifier in
  { e with classifier = t }

;;

let rec typecheck (e : exprU) : expr =

  let e = kindcheck_expr e in
  let env' = setFocus (`E e) in
  let tRes = e.classifier in
  Ctx.inenv env' begin fun _ ->
  match e.term with

      `App( f, a ) ->

          let f  = kindcheck_expr f in
          let a  = kindcheck_expr a in

          let tD = newTMeta e.loc in
          typUnify f.classifier (a.classifier **> tD) ;
          typUnify tD tRes ;
          let _ =
            (* Hack: try to see whether it is easy to determine the type of `a`, without
               picking a specific variable when overloading is ambiguous. This typically
               leads to more information for typechecking `f` and disambiguating constants
               there. *)
            if getResolveAmbiguousVars() then
              Ctx.inenv (setResolveAmbiguousVars false)
                        (fun _ -> try ignore(typecheck a) with _ -> ())
          in
          let f = typecheck f in
          let a = typecheck a in
          { e with term = `App(f, a) }

    | `Lam( binder, tD, body ) ->

      (* let (binder', tD, body, env') = Ctx.bench "typechecking.lam" (lazy begin *)
        let body    = kindcheck_expr body in
        let tD      = kindcheck_type tD in
        let _       = typUnify (tD **> body.classifier) tRes in
        let env'    = addBvar (string_of_name binder) tD in
        let binder' = fixAbstractBinder binder in
      (*         binder', tD, body, env' *)
      (* end) in *)
      let body = Ctx.inenv env' (fun _ -> typecheck body) in
      { e with term = `Lam( binder', tD, body ) }

    | `Const(o) -> { e with term = `Const(o) }

    | `Var(s, Some idx) ->

      let typ = lookupIndex idx e.loc in
      typUnify typ tRes ;
      { e with term = `Var(s, idx) }

    | `Var(`Anon, None) -> assert false

    | `Var(`Concrete(s) as n, None)
    | `Var(`Abstract(s, _) as n, None) ->

      (* Ctx.bench "typechecking.var unknown" (lazy begin *)

        let s = string_of_name n in
        let tryBvar () = findUnifiableVar `Bound (findBvar s) e in
        let tryFvar () = findUnifiableVar `Free (findFvar s) e  in
        let tryMeta () = let i = findMeta e.loc s in
                         let index = `Meta, i in
                         let typ = lookupIndex index e.loc in
                         typUnify typ tRes ;
                         index
        in
        let (//) f g () =
          Ctx.choice ~expectedException:(function Not_found | WrongTermVar(_) -> true | _ -> false) f g
        in

        let i  = (tryBvar // (tryFvar // (tryMeta // (fun _ -> raise (WrongTermVar(e)))))) () in
        let n' = fixAbstractName n i in
        { e with term = `Var(n', i) }

      (* end) *)

    | `Annot(ebase, t) ->

      let ebase = kindcheck_expr ebase in
      let t     = kindcheck_type t in
      typUnify t ebase.classifier ;
      typUnify t tRes ;
      let ebase = typecheck ebase in
      { e with term = ebase.term }

    | `Unparsed(s) -> raise (NoGenericParsingYet)
(*
        perform
          t <-- deepChaseType tRes ;
          let parser_for_type t' s loc =
            match t with `Unknown(_) -> failwith (Printf.sprintf "Cannot parse %s of unknown type at %s." s (UChannel.string_of_loc loc))
            | _ -> try (get_expr_parser t) t' s loc with (Peg.IncompleteParse(_) as e) -> raise e | _ -> failwith (Printf.sprintf "Parsing error at %s.\n" (UChannel.string_of_loc loc))
          in
          e <-- parser_for_type t s loc ;
          env'' <-- setfocus e ;
          _ <-- inenv env'' (typUnify e.classifier t) ;
          typecheck e
*)

  end

;;

(* ----------------
   Handling errors.
   ---------------- *)

exception TypingError;;
let typing_handler (type a) (code : unit -> a) : a =

  try code ()
  with

  | UnifyError(t1, t2) ->
    begin
      let e  = getExprFocus () in
      let t1 = prepareTypeForUser t1 in
      let t2 = prepareTypeForUser t2 in
      let s =
        Printf.sprintf "Term of type %a,\n   whereas expected a type of form %a."
                       Typ.print t1 Typ.print t2
      in
      Utils.log_error (UChannel.string_of_span e.loc) s; raise TypingError
    end

  | OccursCheck(i, t) ->
    begin
      let e  = getExprFocus () in
      let tm = prepareTypeForUser { term = `TVar("", Some (`Meta, i), []) ; classifier = () ;
                                    loc = None ; extra = TypExtras.empty () }
      in
      let t  = prepareTypeForUser t in
      let s = Printf.sprintf "Type %a needs to be unified with %a, which contains it."
                 Typ.print tm Typ.print t
      in
      Utils.log_error (UChannel.string_of_span e.loc) s; raise TypingError
    end


  | WrongTermVar(x) ->

    begin

      let t = prepareTypeForUser x.classifier in
      let s = Printf.sprintf "Variable %a with type %a does not exist."
                 (ExprU.print ~debug:false) x Typ.print t
      in
      Utils.log_error (UChannel.string_of_span x.loc) s; raise TypingError

    end

  | WrongTypeVar ->

    begin

      let t = getTypeFocus () in
      let t = prepareTypeForUser t in
      let s = Printf.sprintf "Unknown type variable %a."
                 Typ.print t
      in
      Utils.log_error (UChannel.string_of_span t.loc) s; raise TypingError

    end

  | WrongTypeArity(expected, actual) ->

    begin

      let t = getTypeFocus () in
      let t = prepareTypeForUser t in
      let s = match t.term with `TVar(s, _, _) -> s | _ -> assert false in
      let s = Printf.sprintf "Type %s used with %d arguments instead of %d as defined."
                 s actual expected
      in
      Utils.log_error (UChannel.string_of_span t.loc) s; raise TypingError

    end

  | UnknownType(t) ->

    begin

      let e = getExprFocus () in
      let t = prepareTypeForUser t in
      let s = Printf.sprintf "Could not fully determine type; got as far as %a."
                             Typ.print t
      in
      Utils.log_error (UChannel.string_of_span e.loc) s; raise TypingError

    end

  | InvalidKind(t) ->

    begin

      let t = prepareTypeForUser t in
      let s = Printf.sprintf "The kind %a is invalid." Typ.print t in
      Utils.log_error (UChannel.string_of_span t.loc) s; raise TypingError

    end


  | AbstractionOverType(t) ->

    begin

      let s = Printf.sprintf "Abstraction over type is not allowed here." in
      Utils.log_error (UChannel.string_of_span t.loc) s; raise TypingError

    end

  | RankNPolymorphism(t) ->

    begin

      let s = Printf.sprintf "Rank-N-polymorphism not supported." in
      Utils.log_error (UChannel.string_of_span t.loc) s; raise TypingError

    end

(*
  | e ->

    begin
      let focus = getFocus () in
      let loc = match focus with `E t -> UChannel.string_of_span t.loc | `T t -> UChannel.string_of_span t.loc
        | _ -> "<unknown>"
      in
      let s = Printf.sprintf "In %s:\n  (Unhandled error during typing.)\n" loc in
      Printf.printf "%s" s; raise e
    end
 *)
;;

let typecheck e = Ctx.bench "typechecking" (lazy(typecheck e)) ;;

let typeof (e : exprU) : expr =

  typing_handler (fun _ -> chaseTypesInExpr (typecheck e))

;;

let typedecl (s : string) (t : typ) () : int =
  typing_handler (fun _ -> type_declaration s t)
;;

(* ----------------
   Abbreviations for terms.
   ---------------- *)

let mkLam ?(loc = None) x e () =

  let uA  = newTMeta loc in
  let uB  = newTMeta loc in
  let env = addBvar x uA in
  let e   = Ctx.inenv env e in
  { term = `Lam(`Concrete(x),uA,e) ; classifier = uB ; loc = loc ; extra = ExprExtras.empty () }


let mkLamT ?(loc = None) x t e () =

  let uB  = newTMeta loc in
  let env = addBvar x t in
  let e   = Ctx.inenv env e in
  { term = `Lam(`Concrete(x),t,e) ; classifier = uB ; loc = loc ; extra = ExprExtras.empty () }


let mkLamO ?(loc = None) x ot e =
  match ot with Some t -> mkLamT ~loc:loc x t e | None -> mkLam ~loc:loc x e

let mkApp ?(loc = None) e1 e2 () =
  let e1 = e1 () in
  let e2 = e2 () in
  let uA  = newTMeta loc in
  { term = `App(e1, e2) ; classifier = uA ; loc = loc ; extra = ExprExtras.empty () }

let mkIndexedVar ?(loc = None) ?(name = `Anon) i () =
  let uA = newTMeta loc in
  { term = `Var(name, Some i) ; classifier = uA ; loc = loc ; extra = ExprExtras.empty () }

let mkVar ?(loc = None) s () =
  let uA = newTMeta loc in
  { term = `Var(`Concrete(s), None) ; classifier = uA ; loc = loc ; extra = ExprExtras.empty () }

let mkNameVar ?(loc = None) s () =
  let s' = toNameMeta s in
  { term = `Var(`Concrete(s'), None) ; classifier = !(builtinStringType) ; loc = loc ;
    extra = ExprExtras.empty () }

let mkCapturingVar ?(loc = None) s () =
  let env   = !termenv in
  let bvars = List.map (fun i -> mkIndexedVar ~loc:loc (`Bound, i)) (increasing env.bvars) in
  let res   = List.fold_right (fun e s -> mkApp ~loc:loc s e) bvars (mkVar ~loc:loc s) in
  let res   = res () in
  { res with loc = loc }

let mkAnnot ?(loc = None) e t () =
  let e = e () in
  { term = `Annot(e, t) ; classifier = t ; loc = loc ; extra = ExprExtras.empty () }

let mkUnparsed ?(loc = None) s () =
  let uA = newTMeta loc in
  { term = `Unparsed(s) ; classifier = uA ; loc = loc ; extra = ExprExtras.empty () }

(*
let mkBaseParsed ?(loc = None) s locstart =
  let open Ctx.Monad in
  perform
    uA <-- newTMeta loc ;
    e  <-- begin
      try !default_expr_parser uA s locstart
      with (Peg.IncompleteParse(_) as e) -> raise e
           | _ -> failwith (Printf.sprintf "Parsing error at %s.\n" (UChannel.string_of_loc locstart))
    end;
    return e ;;
*)

let (%@) = mkApp;;
let (~%) = mkVar;;
let (~%%) = mkCapturingVar;;


(* ------------
   Global state.
   ------------ *)

let builtinstate = ref (empty_state ()) ;;
let globalstate  = ref (!builtinstate) ;;

let runterm e state =
  (termstate := state ;
   termenv   := empty_env () ;
   let res = e () in res, !termstate) ;;

let globalterm_do e  =
  let res, state' = runterm e !globalstate in
  globalstate := clearMetas state' ;
  res ;;

let builtin_do e =
  let res, state' = runterm e !builtinstate in
  builtinstate := clearMetas state';
  res ;;

let global_define s typ =
  ignore (globalterm_do (typedecl s typ))
;;

let global_term_reset () =
  globalstate := { !builtinstate with current_testsuite = (!globalstate).current_testsuite }
;;


(* namespace/file loading management *)
let reifyexn e = try `Left(e ()) with exn -> `Right(exn);;
let reflectexn e = match e with `Left(v) -> v | `Right(exn) -> raise exn;;

let enter_module m () =
  let state = !termstate in
  let prev_curmod = state.current_module in
  let curmod = match prev_curmod with None -> m | Some prefix -> prefix ^ "." ^ m in
  termstate := { state with current_module = Some curmod ;
                   module_extension_stack = prev_curmod :: state.module_extension_stack
               }
;;

let global_enter_module m =
  globalterm_do (enter_module m)
;;

let open_module m () =
  let state = !termstate in
  termstate := { state with open_modules = m :: state.open_modules }
;;

let global_open_module m =
  globalterm_do (open_module m)
;;

exception NotInModule;;

let leave_module () =
  let state = !termstate in
  match state.module_extension_stack with
    [] -> raise NotInModule
  | prev_curmod :: stack ->
    termstate := { state with current_module = prev_curmod ; module_extension_stack = stack }
;;

let global_leave_module () =
  globalterm_do leave_module
;;


let global_module_do m f =
  global_enter_module m ;
  let res = reifyexn f in
  global_leave_module () ;
  reflectexn res
;;

let global_restore_post_file_import state' =
  let state = !globalstate in
  globalstate := { state with current_module = state'.current_module ;
                              module_extension_stack = state'.module_extension_stack ;
                              open_modules = state'.open_modules ;
                              current_directory = state'.current_directory ;
                              current_testsuite = state'.current_testsuite ;
                              last_query = None
                 }
;;

type syntax_type = [ `Makam | `Markdown ] ;;

let syntax_type_of (s: string) =
  match Path.ext (Path.of_string s) with
    Some "md" -> Some `Markdown
  | Some "makam" -> Some `Makam
  | _ -> None
;;

let global_load_file_resolved ?modul
    (pars : syntax_type -> string -> unit) (filename : string) =

  let state = !globalstate in
  let fullmodul =
    match state.current_module, modul with
      None, None -> None
    | Some m, None -> Some m
    | None, Some m -> Some m
    | Some m, Some m' -> Some (m ^ "." ^ m')
  in
  let already_loaded =
    match modul with
    | None ->
      (try
         StringSet.mem filename state.globally_loaded_modules
       with Not_found -> false) ||
      (try
         StringSet.mem (Option.get fullmodul) (Dict.find filename state.modules_loaded_in_modules)
       with _ -> false)
    | Some m ->
      (try
         StringSet.mem (Option.get fullmodul) (Dict.find filename state.modules_loaded_in_modules)
       with _ -> false)
  in
  if already_loaded then ()
  else begin

    let cur_dir = Path.of_string filename |> Path.parent |> Path.to_string in
    let syntax = Option.default `Makam (syntax_type_of filename) in
    let updateLoadedModules () =

      let state' = !globalstate in
      match fullmodul with

      | None ->
        globalstate := { state' with globally_loaded_modules =
            StringSet.add filename state'.globally_loaded_modules }

      | Some m ->
        globalstate := { state' with modules_loaded_in_modules =
            Dict.modify_def StringSet.empty filename (StringSet.add m) state'.modules_loaded_in_modules }

    in

    let doit f =

      globalstate := { !globalstate with current_directory = cur_dir } ;

      match modul with

      | None -> begin
        f () ; updateLoadedModules ()
      end

      | Some m -> begin
        global_module_do m f;
        updateLoadedModules ()
      end

    in

    let original_state = !globalstate in
    let res = reifyexn (fun () -> doit (fun () -> pars syntax filename)) in
    global_restore_post_file_import original_state ;
    reflectexn res

  end
;;
(* ---- ok enough of that *)

exception FileNotFound of string * string list;;
let first_existing_filename userfn fns =
  try List.find Sys.file_exists fns
  with _ -> raise (FileNotFound(userfn, fns))
;;

let global_resolve_cache_filename fn =
  let state = !globalstate in
  if Path.is_absolute (Path.of_string fn) then
    first_existing_filename fn [fn]
  else
    let cons_cache_dir tl =
      match state.cache_directory with
        None -> tl
      | Some dir -> dir :: tl
    in
    let directories = (cons_cache_dir state.included_directories) |> List.map Path.of_string in
    List.map (fun dir -> Path.to_string (Path.concat dir (Path.of_string fn))) directories
    |> first_existing_filename fn
;;

let global_set_cache_directory dir =
  let state = !globalstate in
  globalstate := { state with cache_directory = dir }
;;

let global_get_cache_directory dir =
  let state = !globalstate in
  (!globalstate).cache_directory
;;

let global_resolve_filename fn =
  let state = !globalstate in
  if Path.is_absolute (Path.of_string fn) then
    first_existing_filename fn [fn]
  else
    let directories = (state.current_directory :: state.included_directories) |> List.map Path.of_string in
    List.map (fun dir -> Path.to_string (Path.concat dir (Path.of_string fn))) directories
    |> first_existing_filename fn
;;

let global_add_directory dir =
  let state = !globalstate in
  let resolved_if_existing =
    try
      global_resolve_filename dir
    with FileNotFound _ -> dir
  in
  globalstate := { state with included_directories = state.included_directories ++ [resolved_if_existing] }
;;

let global_load_file ?modul
    (pars : syntax_type -> string -> unit) (filename : string) =
  let filename =
    match syntax_type_of filename with
      Some _ -> filename
    | None -> filename ^ ".makam"
  in
  global_load_file_resolved ?modul:modul pars (global_resolve_filename filename)
;;


let global_typecheck eorig =
  globalterm_do
        (fun () ->
          let e   = eorig () in
          let e'  = typeof e in
          let t   = prepareTypeForUser e'.classifier in
          let e'' = exprAsExprU e' in
          Printf.printf "%a : %a\n" (ExprU.print ~debug:false) e'' Typ.print t)
;;


let global_typecheck_silent eorig  =
  globalterm_do
    (fun () ->
      let e  = eorig () in
      ignore (typeof e))
;;

let global_set_testsuite s =
  globalterm_do (fun () ->
    let state = !termstate in
    termstate := { state with current_testsuite = Some s })
;;

let global_set_last_query q =
  globalterm_do (fun () ->
    let state = !termstate in
    termstate := { state with last_query = q })
;;

(* ----------------------
   Beta-eta normalization.
   ---------------------- *)

module NameUnif = struct
  module Monad = StateEnvMonad.Make(struct
    type env = unit
    type state = nameunifs
  end)
end;;

let inEmptyNameUnif f =
  f { env = () ; state = [] }
;;

type replacement = expr -> int -> expr
let replace replacement e =
  let rec aux c e =
    match e.term with
        `App(e1, e2) -> { e with term = `App(aux c e1, aux c e2) }
      | `Lam(s,t,e') -> { e with term = `Lam(s,t,aux (c+1) e') }
      | `Var(_, (`Bound, _)) -> replacement e c
      | `Var(_, _)  -> e
      | `Const(o)   -> e
  in
  aux 0 e ;;

let shift n e =
  replace (fun e c ->
    match e.term with
        `Var(s, (`Bound, i)) ->
          if i >= c then { e with term = `Var(s, (`Bound, i+n)) } else e
      | _ -> assert false) e ;;

let subst esubst e =
  replace (fun e c ->
    match e.term with
        `Var(s, (_, i)) ->
          if i = c then shift c esubst else e
      | _ -> assert false) e ;;

let substmany esubst e =
  replace (fun e c ->
    match e.term with
        `Var(s, (_, i)) ->
          if c <= i && i - c < List.length esubst then
            shift c (List.nth esubst (i-c))
          else e
      | _ -> assert false) e ;;


let rec is_val (e : expr) : bool =
  match e.term with
    | `App( { term = `Lam(_) }, _ ) -> false
    | `App( { term = `Var(_) }, _ ) -> true
    | `App( e1, _ )                 -> is_val e1
    | `Lam(_) | `Var(_) | `Const(_) -> true

;;


let incorporateName (n : name) (e : expr) : unit NameUnif.Monad.m =
  let open NameUnif.Monad in
  match e.term with
      `Var(n1, (`Bound, _)) | `Var((`Abstract(_) as n1), (`Free, _)) ->
        perform
          state <-- getstate ;
          setstate ( (n1, n) :: state )
    | _ -> return ()
;;

let rec betashort (e : expr) : expr NameUnif.Monad.m =

  let open NameUnif.Monad in
  match e.term with

      `Lam( s, t, ebody ) ->
        perform
          ebody' <-- betashort ebody ;
          return { e with term = `Lam( s, t, ebody' ) }

    | `App( efun, earg ) ->

        (perform
           efun <-- betashort efun ;
           earg <-- betashort earg ;
           match efun.term with
            `Lam( s, t', ebody ) ->
              perform
                _ <-- incorporateName s earg ;
                let res = shift (-1) (subst (shift 1 earg) ebody) in
                if is_val res then return res else betashort res
          | _ -> return { e with term = `App(efun, earg) })


    | _ -> return e
;;

let betashort e = NameUnif.Monad.benchM "beta normalization" (lazy(betashort e)) ;;

let etalong (e : expr) : expr =

  let rec etalong (efocus : expr) (eWithApps : expr -> expr) (apps : int) : expr =

    let etaexpand argsT e =
      let e' = shift (List.length argsT) e in
      let rec aux types e =
        if List.is_empty types then e
        else
        let hd, tl = match types with hd :: tl -> chaseType hd, tl | _ -> assert false in
        match hd, tl with
          | ({ term = `Arrow(t1, t2) } as t), tl ->
            let lam body    = { term = `Lam(`Anon, t1, body) ; classifier = t ; loc = e.loc ; extra = ExprExtras.empty () } in
            let prebody var = { term = `App(e, var) ; classifier = t2 ; loc = e.loc ; extra = ExprExtras.empty () } in
            let var         = { term = `Var(`Anon, (`Bound, List.length tl)) ; classifier = t1 ; loc = UChannel.span_end e.loc ; extra = ExprExtras.empty () } in
            let var'        = etalong var id 0 in
            lam (aux tl (prebody var'))
          | _ -> assert false
      in
      aux argsT e'

    in

    match efocus.term with

        `Lam(s, t, ebody) ->
            assert (apps = 0);
            { efocus with term = `Lam(s, t, etalong ebody id 0) }

      | `App(efun, earg)  ->
            let earg'         = etalong earg id 0 in
            let efocus' focus = { efocus with term = `App(focus, earg') } in
            etalong efun (fun focus -> eWithApps (efocus' focus)) (apps + 1)

      | `Var(_)
      | `Const(_)         ->
        let eWithApps = eWithApps efocus in
        let argsT, _ = gatherArrows efocus.classifier in
        let argsT = List.drop apps argsT in
        etaexpand argsT eWithApps


  and etalong_opt e =

    let countlams =
      let rec aux n e = match e.term with `Lam(_, _, e') -> aux (n+1) e' | _ -> n in
      aux 0 e
    in
    let countarrows = gatherArrows e.classifier |> fst |> List.length in
    if countlams == countarrows then e else etalong e id 0

  in
  etalong_opt e
;;

let etalong e = Benchmark.cumulative "eta normalization" (lazy(etalong e));;

let normalize e =
  let open NameUnif.Monad in
  inEmptyNameUnif begin
      perform
        e' <-- betashort e ;
        return (etalong e')
  end
;;

let typecheck_and_normalize e =
  let e' = typeof e in
  let e', nameunifs = normalize e' in
  let e' = namesForAnonVars e' in
  (e', nameunifs)
;;

let global_typecheck_and_normalize e =

  globalterm_do (fun () ->
    let e = e () in
    let (e', _) = typecheck_and_normalize e in
    let t  = prepareTypeForUser e'.classifier in
    let efinal = exprAsExprU e' in
    Printf.printf "%a : %a\n" (ExprU.print ~debug:true) efinal Typ.print t
  )

;;

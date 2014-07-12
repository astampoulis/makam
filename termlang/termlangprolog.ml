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
open Termlangcanon;;
open Termlangbuiltin;;

type indexN =
  [ `Free | `Bound | `New ] * int ;;

type 'a typinfo = ('a, typ) typedterm ;;

type pattcanonP =
  [ `LamMany of (name * typ) typinfo list * pattneut ]

and  pattneutP =
  [ `AppMany of patthead * pattcanon list * unit typinfo list
  | `Meta of string * int * subst * typ ]

and  pattheadP =
  [ `Var of name * indexN
  | `Const of Obj.t ]

and  subst =
  [ `Subst of pattcanon list * substinv option * unit typinfo list * name list ]

and  substinv = (patthead IMap.t) * (patthead IMap.t)

and  pattcanon = (pattcanonP, typ) typedterm
and  pattneut  = (pattneutP,  typ) typedterm
and  patthead  = (pattheadP,  typ) typedterm ;;

type metamode = [ `General | `Free | `New ] ;;

type prop =
    { patt : pattneut ;
      propmetas : int ;
      proptmetas : int ;
      propnameunifs : nameunifs ;
      prophasrunmetas : bool } ;;

type runState  =
    { rsmetas            : int ;
      rsmeta_level       : int IMap.t ;
      rsmeta_parent      : (pattneut * int) IMap.t ;
      rsmeta_constraints : constraintT list IMap.t ;
      rsmeta_boundnames  : name list IMap.t ;
      rsmeta_mode        : metamode IMap.t ;
      rsconstr_for_pred  : prop list IMap.t ;
      rstermstate        : ctxState ;
      rsmutbacktrack     : StateEnvMutableMonad.backtrack ;
      rslogstackdepth    : int ref ;
      rsopengoals        : (pattneut * runEnv) list ;
      rsmetaswithconstraints : ISet.t ;
      rstraced_predicates : ISet.t
    }

and  runEnv =
    { retemp_constr_for_pred : prop list IMap.t ;
      renvars                : (name * typ) list }

and  constraintT = 
  [ `Unif of name list * pattneut * pattneut
  | `UnifCanon of name list * pattcanon * pattcanon
  | `Demand of int * int option * pattneut * runEnv
  | `RemoveDemand of int * int ]
;;

type 'a stateEnvMonad =
    (runEnv, runState) ctx -> 'a * runState

and  'a twoContMonad =
    { twocont : 'ans . ('ans stateEnvMonad, 'a) successK -> ('ans stateEnvMonad) failK -> 'ans stateEnvMonad }

and  ('ans) failK = 'ans Lazy.t
and  ('ans, 'a) successK = 'a -> 'ans failK -> 'ans ;;


let _DEBUG_DEMAND   : bool ref = ref false ;;
let _DEBUG_CONSTRAINTS : bool ref = ref false ;;
let _BENCHMARK      : bool ref = Benchmark.enabled ;;
let _LOGGING        : bool ref = ref false ;;
let _ONLY_TYPECHECK : bool ref = ref false ;;


let metaindex     (_, idx, _, _) = idx ;;
let metasubst     (_, _, subst, _) = subst ;;
let metasubstmain (_, _, `Subst(s, _, _, _), _) : pattcanon list = s ;;
let metasubstinv  (_, _, `Subst(_, inv, _, _), _) : substinv option = inv ;;

let mut_logstackdepth = ref 0 ;;

(* ------------------ *)
(* The main monad.    *)
(* ------------------ *)

module RunCtx =
  struct
    
    module BaseMonad = 
      struct
	include StateEnvMutableMonad.Make(struct
	  type state = runState ;;
	  type env   = runEnv ;;
	  let  getbt st = st.rsmutbacktrack ;;
	  let  setbt st bt' = { st with rsmutbacktrack = bt' };;
	end);;
      end;;

    (* The following is adapted from "Backtracking, Interleaving and Terminating
       Monad Transformers" by Oleg Kiselyov et al.

       It models backtracking computations as pairs of a success and a failure continuation.
    *)

    module Monad = 
    struct

      type 'a m = 'a twoContMonad ;;

      let return (type a) (e : a) : a m =
	{ twocont = fun ksucceed kfail -> ksucceed e kfail } ;;

      let bind (type a) (type b) (e : a m) (f : a -> b m) : b m =
	{ twocont = fun ksucceed ->
	  e.twocont (fun x -> (f x).twocont ksucceed) } ;;

      let mzero (type a) : a m =
	{ twocont = fun ksucceed kfail -> Lazy.force kfail } ;;

      let mplus (type a) (first : a m) (second : (a m) Lazy.t) : a m =
	{ twocont = fun ksucceed kfail ->
	  first.twocont ksucceed (lazy((Lazy.force second).twocont ksucceed kfail)) };;

      let (//) (type a) (first : a m) (second : (a m) Lazy.t) : a m =
	mplus first second ;;

      let msum (type a) (choices : ((a m) Lazy.t) list) : a m =
	List.fold_left mplus mzero choices ;;

      let lift (type a) (e : a BaseMonad.m) : a m =
	{ twocont = fun ksucceed kfail ->
	  BaseMonad.bind e (fun x -> ksucceed x kfail) } ;;

      let liftl (type a) (e : (a BaseMonad.m) Lazy.t) : a m =
	{ twocont = fun ksucceed kfail ->
	  BaseMonad.bind (Lazy.force e) (fun x -> ksucceed x kfail) } ;;

      let reflect (type a) (e : (a * a m Lazy.t) option) : a m =
	match e with
	    None -> mzero
	  | Some (x,f) -> (return x) // f ;;

      let msplit (type a) (e : a m) : (a * a m Lazy.t) option m =
	let ksucceed res kfail =
	  BaseMonad.return (Some(res, lazy(bind (liftl kfail) reflect)))
	in
	lift (e.twocont ksucceed (lazy(BaseMonad.return None)))
      ;;

      let getall (type a) (e : a m) : a list m =
	let rec aux acc e =
	  bind (msplit e)
	    (function None  -> return (List.rev acc)
	    | Some (hd, tl) -> aux (hd :: acc) (Lazy.force tl))
	in
	aux [] e
      ;;

      let interleave (type a) =
	let rec interleave (e1 : a m) (e2 : (a m) Lazy.t) : a m =
	perform
	  look1 <-- msplit e1 ;
	  match look1 with
	      None -> Lazy.force e2
	    | Some (top1, rest1) -> (return top1) //
	                            (lazy(interleave (Lazy.force e2) rest1))
	in
	interleave
      ;;

      let bfbind (type a) (type b) =
	let rec bfbind (x : a m) (f : a -> b m) : b m =
	perform
	  look1 <-- msplit x ;
	  match look1 with
	      None -> mzero
	    | Some (top1, rest1) -> interleave (f top1) (lazy(bfbind (Lazy.force rest1) f))
	in
	bfbind
      ;;

      let fairsum choices = List.fold_left interleave mzero choices ;;

      let ifte (type a) (type b) (cond : a m) (thn : a -> b m) (els : b m Lazy.t) : b m =
	perform
	  look1 <-- msplit cond ;
	  match look1 with
	      None -> Lazy.force els
	    | Some (top1, rest1) -> (thn top1) // (lazy(bind (Lazy.force rest1) thn))
      ;;

      let once (type a) (e : a m) : a m =
	perform
	  look1 <-- msplit e ;
	  match look1 with
	      None -> mzero
	    | Some (top1, _) -> return top1
      ;;

      let bindlist (type a) (l : (a m) list) : (a list) m =
	List.fold_left (fun mList mElm ->
	                  perform list <-- mList ;
	                          elm  <-- mElm  ;
				  return (list ++ [elm])) (return []) l ;;

      let mapM     (type a) (type b) (f : a -> b m) (l : a list) : (b list) m =
	bindlist (List.map f l) ;;

      let bfbindlist (type a) (l : (a m) list) : (a list) m =
	List.fold_left (fun mList mElm ->
	                  bfbind mList (fun list -> bfbind mElm (fun elm -> return (list ++ [elm]))))
	               (return []) l ;;

      let bfmapM f l = bfbindlist (List.map f l);;

      let foldM    (type a) (type b) (f : a -> b -> a m) (s : a) (l : b list) : a m =
	List.fold_left (fun s e -> 
                        perform s' <-- s ;
	                        f s' e) (return s) l ;;

      let benchM (type a) (s : string) (e : a m) : a m = 
	{ twocont = fun ksucceed kfail ->
	  let start = ref (Benchmark.time ()) in
	  let ksucceed res kfail =
	    let difft = Benchmark.difftime !start in
	    Benchmark.cumulative_add s difft ;
	    let _ = start := Benchmark.time () in
	    ksucceed res kfail
	  in
	  e.twocont ksucceed kfail }
      ;;	    


      let logM (type a) (s : string Lazy.t) (e : a m) : a m =
	if !_LOGGING then begin
	let resnum = ref 1 in
	let stackdepth = !mut_logstackdepth in
	mut_logstackdepth := stackdepth + 1;
	let e s =
	  ifte e
	    (fun res -> Benchmark.log (Benchmark.time (), s, (Printf.sprintf "result %d" (!resnum)), stackdepth) ;
	                resnum := !resnum + 1 ;
			mut_logstackdepth := stackdepth ;
			return res)
	    (lazy(Benchmark.log (Benchmark.time (), s, "fail", stackdepth) ;
		  mut_logstackdepth := stackdepth ;
		  mzero))
	in

	{ twocont = fun ksucceed kfail ->
	  let s' = Benchmark.forcepaused s |> Benchmark.return in
	  Benchmark.log (Benchmark.time (), s', "enter", stackdepth) ;
	  (e s').twocont ksucceed kfail }

	end else e
      ;;

      (* Lifts from the base monad. *)

      let intermlang (type a) (e : unit -> a) : a m =
	lift (let open BaseMonad in
	      perform state <-- getstate ;
	              let (res, termstate') = runterm (fun _ -> typing_handler e) state.rstermstate in
		      setstate { state with rstermstate = termstate' } ;
		      return res)
      ;;
	
      let getstate = lift BaseMonad.getstate ;;

      let getbacktrackstate = lift BaseMonad.getbacktrackstate ;;

      let setstate s = lift (BaseMonad.setstate s) ;;

      let getenv   = lift BaseMonad.getenv ;;

      let getctx   = lift BaseMonad.getctx ;;

      let inenv (type a) (e : runEnv) (m : a m) : a m =
	{ twocont = fun ksucceed kfail ->
	  BaseMonad.inenv e (m.twocont ksucceed kfail) } ;;

      module DynArray = struct
	include BaseMonad.DynArray ;;
	let setM i w a = lift (setM i w a) ;;
	let modifyM i f a = lift (modifyM i f a) ;;
      end;;

      module DictHash = struct
	include BaseMonad.DictHash ;;
	let addM k v a = lift (addM k v a) ;;
	let modify_defM def k f a = lift (modify_defM def k f a) ;;
      end;; 

      module Ref = struct
	include BaseMonad.Ref ;;
	let setM r w = lift (setM r w) ;;
      end;;

    end;;

  end ;;

let moneOrMzero b = if b then RunCtx.Monad.return () else RunCtx.Monad.mzero ;;

(* ------------ *)
(* Basic state. *)
(* ------------ *)

let empty_run_env () =
  { retemp_constr_for_pred = IMap.empty ;
    renvars                = [] }
;;

let empty_run_state termstate =
  { rsmetas = 0 ;
    rsmeta_parent = IMap.empty;
    rsmeta_constraints = IMap.empty;
    rsmeta_level = IMap.empty;
    rsmeta_boundnames = IMap.empty ;
    rsmeta_mode = IMap.empty ;
    rsconstr_for_pred = IMap.empty;
    rstermstate = termstate ;
    rsmutbacktrack = StateEnvMutableMonad.rootbt () ;
    rslogstackdepth = mut_logstackdepth ;
    rsopengoals = [] ; 
    rsmetaswithconstraints = ISet.empty ;
    rstraced_predicates = ISet.empty
  }
;;

let empty_run_ctx termstate =
  { env = empty_run_env () ; 
    state = empty_run_state termstate } ;;

let clearRunMetas state =
  mut_logstackdepth := 0;
  { state with
    rsmetas = 0; rsmeta_parent = IMap.empty ;
    rsmeta_level = IMap.empty;
    rsmeta_constraints = IMap.empty;
    rsmeta_boundnames = IMap.empty;
    rsmeta_mode = IMap.empty ;
    rstermstate = clearMetas state.rstermstate ;
    rsmetaswithconstraints = ISet.empty ;
    rsopengoals = [] }
;;

let builtinprologstate = ref (empty_run_state !globalstate) ;;
let globalprologstate = ref (empty_run_state !globalstate) ;;


(* A hack to make readonly/readwrite operations without backtracking faster & easier. *)
let tempstate = ref (empty_run_state (empty_state ())) ;;
let tempenv = ref (empty_run_env ()) ;;

let inmonad ?(statewrite = false) e =
  let open RunCtx.Monad in
  perform
    ctx <-- getctx ;
    let res = (tempstate := ctx.state ;
	       tempenv   := ctx.env ;
	       e ())
    in
    if statewrite
    then (perform setstate !tempstate ;
	          return res)
    else (return res)
;;

let intermlang e =
  let res, termstate' = runterm e (!tempstate).rstermstate in
  tempstate := { !tempstate with rstermstate = termstate' } ;
  res
;;

let logM s e =
  let open RunCtx.Monad in
  perform
    state <-- getstate ;
    \ tempstate := state ;
    logM s e
;;

let benchM s e = RunCtx.Monad.benchM s e ;;

let profileM benchname logname e =
  logM logname (RunCtx.Monad.benchM benchname e)
;;

let log logname e =
  if !_LOGGING then
    (let stackdepth = !mut_logstackdepth in
     mut_logstackdepth := stackdepth + 1;
     let logname = Benchmark.forcepaused logname |> Benchmark.return in
     Benchmark.log (Benchmark.time (), logname, "enter", stackdepth) ;
     let res = Benchmark.force e in
     let status = match res with `Left _ -> "result 1" | `Right _ -> "fail" in
     Benchmark.log (Benchmark.time (), logname, status, stackdepth) ;
     mut_logstackdepth := stackdepth ;
     Benchmark.return res)
  else Lazy.force e ;;

let magiclog logname e = 
  if !_LOGGING then
    (let stackdepth = !mut_logstackdepth in
     mut_logstackdepth := stackdepth + 1;
     let logname = Benchmark.forcepaused logname |> Benchmark.return in
     Benchmark.log (Benchmark.time (), logname, "enter", stackdepth) ;
     _LOGGING := false ;
     let res = Benchmark.forcepaused e in
     _LOGGING := true ;
     let status = match res with `Left _ -> "result 1" | `Right _ -> "fail" in
     Benchmark.log (Benchmark.time (), logname, status, stackdepth) ;
     mut_logstackdepth := stackdepth ;
     Benchmark.return res)
  else Lazy.force e ;;


let bench s e = Benchmark.cumulative s e ;;
  
let profile benchname logname e = bench benchname (lazy(log logname e)) ;;



(* ------------------------- *)
(* Extra information modules *)
(* ------------------------- *)

type pattextras = { renormneed : [ `Never | `Cached of pattcanon | `Maybe ] ref } ;;

module PattExtras = struct
  module Aux : DeferredType.Type = struct
    type t = pattextras ;;
    let empty () = { renormneed = ref `Maybe } ;;
    let uniquetag = 3 ;;
  end ;;
  include DeferredType.Make(Aux) ;;
end ;;


(* -------------------------------------------- *)
(* Auxiliary functions for manipulating patt's. *)
(* -------------------------------------------- *)

let gatherApps (e : expr) : expr * expr list * unit typinfo list =
  let rec aux e acc tacc =
    match e.term with
	`App( e1, e2 ) -> aux e1 ( e2 :: acc ) ( { e with term = () } :: tacc )
      | _              -> e, acc, tacc
  in
  aux e [] []
;;

let reapplyApps (pf : expr) (pargs : expr list) (tapps : unit typinfo list) =
  List.fold_left2 
    (fun cur parg tapp -> { tapp with term = `App(cur, parg) })
    pf pargs tapps
;;


let alphaSanitizeMany ?(bound=[]) (es : expr list) : expr list =
  let fixname bound n =
    match n with
      `Concrete(s) -> s
    | `Abstract(s,_) -> s ^ "_" ^ (List.length bound |> string_of_int)
    | `Anon -> "x_" ^ (List.length bound |> string_of_int)
  in
  let metas : string IMap.t Dict.t ref = ref Dict.empty in
  let meta_get s i =
    if String.starts_with s "_" then s else
    let curmetas = !metas in
    let curmetas', s' =
      match Dict.Exceptionless.find s curmetas with
      |	Some imap ->
	(match IMap.Exceptionless.find i imap with
	| Some s -> curmetas, s
	| None -> let s' = s ^ "_" ^ (string_of_int i) in
		  Dict.modify s (IMap.add i s') curmetas, s')
      | None -> Dict.add s (IMap.singleton i s) curmetas, s
    in
    metas := curmetas' ;
    s'
  in
  let rec aux bound e =
    match e.term with
      `Lam(s,t,e') ->
	let s' = fixname bound s in
	let bound' = s' :: bound in
	{ e with term = `Lam(`Concrete(s'),t,aux bound' e') }
    | `App(e1,e2)  -> { e with term = `App(aux bound e1, aux bound e2) }
    | `Var(_,(`Bound,i)) -> { e with term = `Var(`Concrete(try List.nth bound i with _ -> "!!"), (`Bound, i)) }
    | `Var(`Concrete(s), (`Meta,i)) -> let s' = meta_get s i in
				       { e with term = `Var(`Concrete(s'), (`Meta, i)) }
    | _ -> e
  in
  List.map (aux bound) es
;;

let alphaSanitize ?(bound=[]) (e : expr) : expr =
  match alphaSanitizeMany ~bound:bound [e] with
    [e'] -> e'
  | _ -> assert false
;;


let pattcanonShift, pattneutShift, pattheadShift =

  let rec pattcanonShift n c (e : pattcanon) : pattcanon =

    match e.term with
	`LamMany(binders, body) ->
	  let c' = c + List.length binders in
	  { e with term = `LamMany(binders, pattneutShift n c' body) }

  and pattneutShift n c (e : pattneut) : pattneut =
    
    match e.term with
	`AppMany(hd, args, typs) ->
	  { e with term = `AppMany(pattheadShift n c hd,
				   List.map (pattcanonShift n c) args, typs) }

      | `Meta(s, i, subst, typfull) ->
	let subst' = pattsubstShift n c subst in
	{ e with term = `Meta(s, i, subst', typfull) }


  and pattheadShift n c (e : patthead) : patthead =
    
    match e.term with
      | `Var(s, (`Bound, i)) when i >= c -> { e with term = `Var(s, (`Bound, i+n)) }
      | _ -> e
	
  and pattsubstShift n c (e : subst) : subst =
    
    match e with
	`Subst(subst, substinv, typs, names) ->
	  `Subst(List.map (pattcanonShift n c) subst, None, typs, names)

  in
  (fun n -> if n = 0 then id else pattcanonShift n 0),
  (fun n -> if n = 0 then id else pattneutShift n 0),
  (fun n -> if n = 0 then id else pattheadShift n 0)
;;

let pattheadToCanon (p : patthead) : pattcanon =

  let neut = { p with term = `AppMany(p, [], []) } in
  let canon = { p with term = `LamMany([], neut) } in
  canon

;;  

let pattneutToCanon (p : pattneut) : pattcanon =
  { p with term = `LamMany([], p) }
;;


let rec pattEtaShort (p : pattcanon) : patthead option =
  
  let `LamMany(lams, body) = p.term in

  match body.term with

      `Meta(_) -> None

    | `AppMany(hd, args, _) -> 

      let level = List.length lams in
      let isbound idx p =

	match p.term with
	  | `LamMany([], { term = `AppMany( { term = `Var(_, (`Bound, j)) }, [], [] ) })
	      when idx = j -> true
	  | _ -> begin
	    match pattEtaShort p with
	      |	Some { term = `Var(_, (`Bound, j)) } when idx = j -> true
	      | _ -> false
	  end
	
      in
      let isidsubst =

	List.length args == level &&
	List.for_all2 isbound (decreasing level) args

      in

      if isidsubst then
	Some (pattheadShift (-level) hd)
      else
	None

;;

let invertSubst (subst : pattcanon list) : substinv option =

  let nth_set (i : int) (sinv : patthead IMap.t) (p : patthead) : (patthead IMap.t) option =

    match IMap.Exceptionless.find i sinv with
	Some p' -> if p = p' then Some sinv else None
      | None    -> Some(IMap.add i p sinv)

  in

  let rec aux (subst : pattcanon list) (i : int) (newsinv : patthead IMap.t) (boundsinv : patthead IMap.t) : substinv option =

    match subst with

	[] -> Some (newsinv, boundsinv)

      | hd :: tl ->

	let e = pattEtaShort hd in

	(match e with

	  | Some( { term = `Var(s,(`Bound,j)) } as e' ) ->
	      
	    let e' = { e' with term = `Var(s, (`Bound, i)) ; extra = PattExtras.empty () } in
	    (match nth_set j boundsinv e' with
		Some boundsinv' -> aux tl (i-1) newsinv boundsinv'
	      | None -> None)

	  | Some( { term = `Var(s,(`New,j)) } as e' ) ->

	    let e' = { e' with term = `Var(s, (`Bound, i)) ; extra = PattExtras.empty () } in
	    (match nth_set j newsinv e' with
		Some newsinv' -> aux tl (i-1) newsinv' boundsinv
	      | None -> None)
	    
	  | _ -> None)

  in

  aux subst ((List.length subst) - 1) IMap.empty IMap.empty

;;


let invertSubstNeut (p : pattneut) : pattneut =

  match p.term with

    `Meta(s,i,`Subst(subst,_,typs,bound),typfull) ->
      
      let inv = invertSubst subst in
      { p with term = `Meta(s,i,`Subst(subst,inv,typs,bound),typfull) }

  | `AppMany _ -> p
	
;;


let freshenPatt (newnvar : int) (e : pattneut) : pattneut =

  let rec aux_canon c e =

    match e.term with
	
	`LamMany(binders, e') ->

	  let n = List.length binders in
	  { e with term = `LamMany(binders, aux_neut (c+n) e') }

  and aux_neut c e =

    match e.term with

      | `AppMany(hd, args, typs) ->
	{ e with term = `AppMany(aux_head c hd, List.map (aux_canon c) args, typs) }

      | `Meta(s, i, subst, typfull) ->
	
	let subst' = aux_subst c subst in
	{ e with term = `Meta(s, i, subst', typfull) }

  and aux_head c e =

    match e.term with
      
      | `Var(s, (`Bound, i)) when i = c -> { e with term = `Var(s, (`New, newnvar)) }

      | _ -> e

  and aux_subst c e =
    
    match e with
	
	`Subst(subst, substinv, typs, names) ->
	  
	  let subst' = List.map (aux_canon c) subst in
	  `Subst(subst', None, typs, names)

  in

  aux_neut 0 e

;;

let exprToPatt (e : expr) : pattneut =

  let rec gatherLam bound lams (e : expr) =
    match e with
	{ term = `Lam(s,t,e') } ->
	  gatherLam (s :: bound) ({ e with term = (s,t) } :: lams) e'
      | _ -> bound, List.rev lams, e
  in

  let rec aux_canon bound (e : expr) : pattcanon =

    match e.term with
      | `Lam(_) -> 
	  
	let bound', lams, body = gatherLam [] [] e in
	{ e with term = `LamMany(lams, aux_neut bound' body) ; extra = PattExtras.empty () }

      | _ ->

	let body = aux_neut bound e in
	{ e with term = `LamMany([], body) ; extra = PattExtras.empty () }
	       
  and aux_neut bound (e : expr) : pattneut =
    
    let ef, eargs, tapps = gatherApps e in
    let eargs' = List.map (aux_canon bound) eargs in

    match ef.term with

      |	`Var(s, (`Free, i)) ->
	  { e with term = `AppMany( { ef with term = `Var(s, (`Free, i)) ; extra = PattExtras.empty () },
				    eargs', tapps ) ; extra = PattExtras.empty () }

      | `Var(s, (`Bound, i)) ->
	  { e with term = `AppMany( { ef with term = `Var(s, (`Bound, i)) ; extra = PattExtras.empty () },
				    eargs', tapps ) ; extra = PattExtras.empty () }

      | `Const(o) ->
	  { e with term = `AppMany( { ef with term = `Const(o) ; extra = PattExtras.empty () }, eargs', tapps )
	         ; extra = PattExtras.empty () }

      | `Var(`Concrete(s), (`Meta, i)) ->
	let subst = `Subst(eargs', None, tapps, bound) in
	{ e with term = `Meta(s, i, subst, ef.classifier) ; extra = PattExtras.empty () }

      | _ -> failwith "expect fully annotated term"

  in
  Benchmark.cumulative "exprToPatt" (lazy(aux_neut [] e))

;;

(* TODO. indentation/clean up and so on up to here so far. *)
exception NewVarUsed ;;
let pattneutToExpr, pattcanonToExpr, pattheadToExpr =

  let rec aux_canon fvars (p : pattcanon) : expr =

    match p.term with
	`LamMany(binders, body) ->
	  let body' = aux_neut fvars body in
	  List.fold_right
	    (fun ( { term = (s,t) } as elm ) body ->
	      { elm with term = `Lam(s,t,body) ; extra = ExprExtras.empty () })
	    binders body'

  and aux_appmany (e : expr) (l : expr list) (l' : unit typinfo list) =

    List.fold_left2
      (fun body arg typ ->
	{ typ with term = `App(body, arg) ; extra = ExprExtras.empty () })
      e l l'
	    
  and aux_neut fvars (p : pattneut) : expr =

    match p.term with
	`AppMany(hd, args, typs) ->
	  let hd' = aux_head fvars hd in
	  let args' = List.map (aux_canon fvars) args in
	  aux_appmany hd' args' typs

      | `Meta(s,i,subst,typfull) ->

	let subst, typs = aux_subst fvars subst in
	let head  = { p with term = `Var(`Concrete(s), (`Meta, i)) ; classifier = typfull ;
	              extra = ExprExtras.empty () }
	in
	aux_appmany head subst typs
	    
  and aux_head fvars (p : patthead) : expr =

    match p.term with

      | `Var(s, (`Bound, i))  -> { p with term = `Var(s, (`Bound, i)) ; extra = ExprExtras.empty () }
      | `Var(s, (`Free, i))   -> { p with term = `Var(s, (`Free, i)) ; extra = ExprExtras.empty () }
      | `Var(s, (`New, i)) when fvars < 0 -> raise NewVarUsed
      | `Var(s, (`New, i))    -> { p with term = `Var(s, (`Free, i+fvars)) ; extra = ExprExtras.empty () }
      | `Const(o)             -> { p with term = `Const(o) ; extra = ExprExtras.empty () }

  and aux_subst fvars (p : subst) : expr list * unit typinfo list =
    
    match p with
	`Subst(subst, substinv, typs, names) ->
	List.map (aux_canon fvars) subst, typs

  in

  let timername = "pattToExpr" in
  (fun fvars p -> Benchmark.cumulative timername (lazy(aux_neut fvars p))),
  (fun fvars p -> Benchmark.cumulative timername (lazy(aux_canon fvars p))),
  (fun fvars p -> Benchmark.cumulative timername (lazy(aux_head fvars p)))  

;;


let idSubst (ts : typ list) (bound : name list) : pattcanon list =

  let n = List.length ts in
  let bound = bound |> List.rev |> List.take n in
  let bound = if List.length bound < n then bound ++ (decreasing (n-List.length bound) |> List.map (fun i -> `Anon)) else bound in
  let bs = List.mapi (fun i (s,t) -> { term = `Var(s, (`Bound, n-i-1)) ; classifier = t ; loc = None ; extra = PattExtras.empty () }) (List.combine bound ts) in
  let bs' = List.map pattheadToCanon bs in
  bs'
;;

let getIntermediateArrows (ts : typ list) (t : typ) l =
  
  if ts = [] then [], t
  else
    (let tres, interm =
       List.fold_right (fun elm (t, interm) ->
	 let t' = 
	   { term = `Arrow(elm, t) ; classifier = () ;
	     loc = UChannel.combine_span elm.loc t.loc ; extra = TypExtras.empty () }
	 in
	 t', (t' :: interm))
	 ts (t, [t])
     in
     let interm = List.tl interm |> List.map (fun t -> { term = () ; classifier = t ; loc = l ; extra = TypExtras.empty () }) in
     interm, tres)
;;

let intersectSubst (subst1 : pattcanon list) (subst2 : pattcanon list) : pattcanon list =

  let gethd (p : pattcanon) : patthead option =
    match p.term with
	`LamMany([], body) ->
	  (match body.term with
	      `AppMany(hd, [], []) -> Some hd
	    | _ -> None)
      | _ -> None
  in
  
  List.combine subst1 subst2 |>
  List.filter_map
  (fun (e1, e2) ->
    match gethd e1, gethd e2 with
      | Some { term = `Var(_, (k, n)) }, Some { term = `Var(_, (k', n')) }
	when  k = k' && n = n'
		-> Some e1
      | _ -> None)

;;

(* -------- printing patt delegates to printing for expr. --------- *)
module PattPrinter =
  functor (P : sig
    type t
    val pattToExpr : int -> t -> expr
  end) ->
struct

  let print oc (p : P.t) =
    let e = P.pattToExpr (!globalstate).fvars p in
    let e = exprAsExprU e in
    ExprU.print ~debug:false oc e
  ;;

  let alphaSanitizedPrint oc p =
    let e = P.pattToExpr (!globalstate).fvars p in
    let e = alphaSanitize e in
    let e = exprAsExprU e in
    ExprU.print ~debug:false oc e
  ;;

  let alphaSanitizedPrintMany ps =
    let es = List.map (P.pattToExpr (!globalstate).fvars) ps in
    let es = alphaSanitizeMany es in
    let es = List.map exprAsExprU es in
    List.map (fun e -> let strout = IO.output_string () in
		       ExprU.print ~debug:false strout e;
		       IO.close_out strout) es
  ;;
    
end;;

module Pattneut = PattPrinter(struct
  type t = pattneut
  let pattToExpr = pattneutToExpr
end);;

module Pattcanon = PattPrinter(struct
  type t = pattcanon
  let pattToExpr = pattcanonToExpr
end);;

module Patthead = PattPrinter(struct
  type t = patthead
  let pattToExpr = pattheadToExpr
end);;

module CheapPrint = struct

  let name oc (n : name) =
    match n with
      `Concrete(s) -> Printf.fprintf oc "%s" s
    | _ -> Printf.fprintf oc "?"
  ;;

  let max_depth = 1 ;;
  let rec neut depth oc (p : pattneut) =
    if depth > max_depth then Printf.fprintf oc "..." else
    match p.term with
    | `AppMany({ term = `Var(_, (`New, idx)) }, [], _) ->
	Printf.fprintf oc "ν%d" idx
    | `AppMany({ term = `Var(s, _) }, [], _) ->
	Printf.fprintf oc "%a" name s
    | `AppMany({ term = `Var(s, _) }, args, _) ->
        let depth' = depth + 1 in
	Printf.fprintf oc "(%a %a)" name s (List.print ~sep:" " ~first:"" ~last:"" (canon depth')) args
    | `AppMany({ term = `Const(_) ; classifier = t }, _, _) ->
	Printf.fprintf oc "[:%a]" Typ.print t
    | `Meta(_,idx,`Subst(subst,_,_,_),_) ->
      let state = !tempstate in
      let rec aux idx =
        (match IMap.Exceptionless.find idx state.rsmeta_parent with
	  Some ({ term = `Meta(_, idx', _, _) }, _) -> aux idx'
	| Some (p, _) -> neut depth oc p
	| None -> Printf.fprintf oc "_/%d" (List.length subst))
      in
      aux idx
  and canon depth oc (p : pattcanon) =
    match p.term with
      `LamMany(_, body) -> neut depth oc body
  let neutdepth d oc p = neut (-d) oc p
  let canondepth d oc p = canon (-d) oc p
  let neut oc p = neut 0 oc p 
  let canon oc p = canon 0 oc p

end;;

let highlightMetas (p : pattneut) : pattneut =
  let rec auxneut p =
    match p.term with
      `AppMany(hd, args, argsinfo) -> { p with term = `AppMany(hd, List.map auxcanon args, argsinfo) }
    | `Meta(s,i,subst,typfull) -> { p with term = `Meta(s,i,subst,typfull) }
  and auxcanon p =
    match p.term with
      `LamMany(info, body) -> { p with term = `LamMany(info, auxneut body) }
  in
  auxneut p
;;


(* ------------  runtime : state manipulation functions --------------------- *)

module DynArray = RunCtx.Monad.DynArray ;;
module DictHash = RunCtx.Monad.DictHash ;;

let addRunMeta_mutable ?(mode = `General) level = 
  let state = !tempstate in
  let env = !tempenv in
  let i = state.rsmetas in
  let level' = match level with Some l -> l | None -> List.length env.renvars in
  let state' =
    { state with rsmetas = state.rsmetas + 1 ;
      rsmeta_constraints  = IMap.add i [] state.rsmeta_constraints ;
      rsmeta_level = IMap.add i level' state.rsmeta_level ;
      rsmeta_mode = IMap.add i mode state.rsmeta_mode ;
    }
  in
  tempstate := state' ;
  i
;;

let addRunMeta ?(mode = `General) level = 
  inmonad ~statewrite:true (fun _ -> addRunMeta_mutable ~mode:mode level)
;;

let getMetaParent_mutable (i : int) : (pattneut * int) option =
  IMap.Exceptionless.find i !tempstate.rsmeta_parent
;;

let getMetaParent (i : int) : (pattneut * int) option RunCtx.Monad.m =
  inmonad (fun _ -> getMetaParent_mutable i);;

let setMetaParent_mutable (i : int) ?(substlen = 0) (p : pattneut) : unit =
  let state = !tempstate in
  let state' = { state with rsmeta_parent = IMap.add i (p, substlen) state.rsmeta_parent } in
  tempstate := state'
;;
  

let setMetaParent (i : int) ?(substlen = 0) (p : pattneut) : unit RunCtx.Monad.m =
  inmonad ~statewrite:true (fun _ -> setMetaParent_mutable i ~substlen:substlen p)
;;

let addConstraint_mutable (i1 : int) (c : constraintT) : unit =
  let state = !tempstate in
  tempstate := { state with rsmeta_constraints = IMap.modify i1
	                                      (fun x -> c :: x)
					      state.rsmeta_constraints ;
                            rsmetaswithconstraints = ISet.add i1 state.rsmetaswithconstraints }
;;
  
let addConstraint (i1 : int) (c : constraintT) : unit RunCtx.Monad.m =
  inmonad ~statewrite:true (fun _ -> addConstraint_mutable i1 c)
;;


let clearConstraints_mutable (i : int) : unit =
  let state = !tempstate in
  tempstate := { state with rsmeta_constraints = IMap.modify i (fun x -> []) state.rsmeta_constraints ;
                            rsmetaswithconstraints = ISet.remove i state.rsmetaswithconstraints }
;;

let clearConstraints (i : int) : unit RunCtx.Monad.m = inmonad ~statewrite:true (fun _ -> clearConstraints_mutable i);;

let getConstraints_mutable (i : int) : constraintT list =
  let state = !tempstate in
  let res = IMap.find i state.rsmeta_constraints in
  clearConstraints_mutable i ;
  List.rev res
;;
  
let getConstraints (i : int) : constraintT list RunCtx.Monad.m = inmonad ~statewrite:true (fun _ -> getConstraints_mutable i);;

let setConstraints_mutable (i : int) (x : constraintT list) : unit =
  let state = !tempstate in
  tempstate := { state with rsmeta_constraints = IMap.modify i (fun _ -> x) state.rsmeta_constraints ;
                            rsmetaswithconstraints = if List.is_empty x then ISet.remove i state.rsmetaswithconstraints else ISet.add i state.rsmetaswithconstraints }
;;

let setConstraints (i : int) (x : constraintT list) : unit RunCtx.Monad.m =
  inmonad ~statewrite:true (fun _ -> setConstraints_mutable i x)
;;

let getOpenGoals () : (pattneut * runEnv) list RunCtx.Monad.m =
  inmonad ~statewrite:true (fun _ -> let res = (!tempstate).rsopengoals |> List.rev in
				     tempstate := { !tempstate with rsopengoals = [] };
				     res)
;;

let addOpenGoal_mutable (p : pattneut) (e : runEnv) : unit =
  tempstate := { !tempstate with rsopengoals = (p, e) :: (!tempstate).rsopengoals }
;;


let getMetaLevel_mutable (i : int) : int = IMap.find i (!tempstate).rsmeta_level ;;

let getMetaLevel (i : int) : int RunCtx.Monad.m = inmonad (fun _ -> getMetaLevel_mutable i);;

let setMetaLevel_mutable (i : int) (l : int) : unit =
  let state = !tempstate in
  tempstate := { state with rsmeta_level = IMap.modify i (fun _ -> l) state.rsmeta_level }
;;

let setMetaLevel (i : int) (l : int) : unit RunCtx.Monad.m =
  inmonad ~statewrite:true (fun _ -> setMetaLevel_mutable i l);;

let getMetaMode_mutable (i : int) : metamode = IMap.find i (!tempstate).rsmeta_mode ;;

let getMetaMode (i : int) : metamode RunCtx.Monad.m =
  inmonad (fun _ -> getMetaMode_mutable i) ;;

let setMetaMode_mutable (i : int) (m : metamode) : unit =
  let state = !tempstate in
  tempstate := { state with rsmeta_mode = IMap.modify i (fun _ -> m) state.rsmeta_mode }
;;

let setMetaMode (i : int) (m : metamode) : unit RunCtx.Monad.m =
  inmonad ~statewrite:true (fun _ -> setMetaMode_mutable i m);;

let chaseName_mutable (n : name) : name =
  let rec chase n = 
    match n with
      `Abstract(s, i) -> (match getMetaParent_mutable i with
	                       None -> n
			     | Some ({ term = `Meta(_,j,_,_) }, _) when i == j -> n
			     | Some ({ term = `Meta(_,j,_,_) }, _) -> chase (`Abstract(s, j))
			     | Some ({ term = `AppMany({ term = `Const(s) }, _, _) }, _) -> `Concrete(Obj.obj s)
			     | _ -> assert false)
      | n -> n
  in
  chase n
;;

let chaseName (n : name) : name RunCtx.Monad.m = inmonad (fun _ -> chaseName_mutable n) ;;


let pattMeta ?(subst = `Subst([], Some (IMap.empty, IMap.empty), [], []))
             ?(loc = None)
	     name idx typ : pattneut =
  let typfull = match subst with `Subst(_, _, hd :: _, _) -> hd.classifier | _ -> typ in
  { term = `Meta(name, idx, subst, typfull) ;
    classifier = typ ;
    loc = loc ; extra = PattExtras.empty () }
;;    


(* we could reuse normal higher-order pattern matching to do name unification,
   but the code that follows is simple first-order unification and thus much faster
   (it does though silently assume various things, e.g. no extra constructors for the string type, etc.) *)
let nameUnify_mutable (n1 : name) (n2 : name) : name =
  let n1' = chaseName_mutable n1 in
  let n2' = chaseName_mutable n2 in
  let _ = if !_DEBUG_NAMES then Printf.printf " ~N %s ~N %s (actually %s ~N %s)\n%!" (string_of_name n1) (string_of_name n2) (string_of_name n1') (string_of_name n2') in
  match n1', n2' with
      `Concrete(s1), `Concrete(s2) -> (if !_DEBUG then Printf.printf "name clash between %s and %s\n%!" s1 s2);
	                              n1'
    | `Concrete(s), `Abstract(_, i)
    | `Abstract(_, i), `Concrete(s) -> (setMetaParent_mutable i (pattneutString s) ;
                                        `Concrete(s))
    | `Abstract(_, i1), `Abstract(_, i2) when i1 = i2 -> n1'
    | `Abstract(s1, i1), `Abstract(_, i2) ->
         (setMetaParent_mutable i1 (pattMeta s1 i2 _tString) ;
	  n2')
    | `Anon, n -> n
    | n, `Anon -> n
;;


let nameUnify n1 n2 = benchM "name unification" (inmonad ~statewrite:true (fun _ -> nameUnify_mutable n1 n2)) ;;


let updateMetaBoundNames_mutable index subst : unit =

  let pattGuessName (p : pattcanon) : name =
    match p with
      { term = `LamMany([], { term = `AppMany( { term = `Var(n, (`New, _)) }, [], _) }) }
    | { term = `LamMany([], { term = `AppMany( { term = `Var(n, (`Bound, _)) }, [], _) }) } -> n
    | _ ->
      (match pattEtaShort p with
	Some { term = `Var(n, (`New, _)) } | Some { term = `Var(n, (`Bound, _)) } -> n
      | _ -> `Anon)
  in

  (* first, construct empty anon list/get the existing list for bound names *)
  (* then, extract names from current subst, whenever things look like vars *)
  (* last, unify the names at the same positions *)

  let state = !tempstate in
  let n = List.length subst in
  let names = try IMap.find index state.rsmeta_boundnames with _ -> List.make n `Anon in
  let names, extranames =
    if List.length names < n then
      names ++ (List.make (n - List.length names) `Anon), []
    else if List.length names > n then
      List.take n names, List.drop n names
    else
      names, []
  in
  let substnames = List.map pattGuessName subst in
  let _ = if !_DEBUG_NAMES then Printf.printf " ~N name update for Meta[%d]\n" index in
  let names' = List.map2 nameUnify_mutable names substnames in
  let _ = if !_DEBUG_NAMES then Printf.printf " ~N name update for Meta[%d] ends\n" index in
  let state = !tempstate in
  let names' = names' ++ extranames in
  let state' =
    { state with rsmeta_boundnames = IMap.modify_def names' index (fun _ -> names') state.rsmeta_boundnames }
  in
  tempstate := state'
;;

let updateMetaBoundNames index subst =
  inmonad ~statewrite:true (fun _ -> updateMetaBoundNames_mutable index subst) ;;


let rec pattcanonUpdateMetaBoundNames_mutable (p : pattcanon) : unit =
  match p.term with
    `LamMany(_,body) -> pattneutUpdateMetaBoundNames_mutable body

and pattneutUpdateMetaBoundNames_mutable (p : pattneut) : unit =

  match p.term with
    `AppMany(head, args, _) -> List.iter pattcanonUpdateMetaBoundNames_mutable args
  | `Meta(_,i,`Subst(subst,_,_,_),_) -> updateMetaBoundNames_mutable i subst

;;

let pattcanonUpdateMetaBoundNames p =
  inmonad ~statewrite:true (fun _ -> pattcanonUpdateMetaBoundNames_mutable p) ;;

let pattneutUpdateMetaBoundNames p  =
  inmonad ~statewrite:true (fun _ -> pattneutUpdateMetaBoundNames_mutable p)  ;;

(* eta re-expansion for patterns. *)

let countArrows (t : typ) : int * typ =
  let rec aux acc (t : typ) =
    match chaseType t with
      { term = `Arrow(_, t) } -> aux (acc+1) t
    | last -> acc, last
  in
  aux 0 t
;;

let rec pattcanonEtaLong_mutable ?(only_top = false) (e : pattcanon) : pattcanon =

  match e.term with
    
    `LamMany( lams, body ) ->
      
      let nlams = List.length lams in
      let narrows, rng = countArrows e.classifier in
      assert (nlams <= narrows) ;
      if only_top && nlams == narrows then begin
	
        (* optimization: keep info to see whether renormalization will ever be needed *)
        (* let extra = PattExtras.castout e.extra in
	let renormneed = match rng.term with `TVar(_, Some (`Meta, _), _) -> `Maybe | _ -> `Never in
	perform
	  _ <-- Ref.setM extra.renormneed renormneed ; *)
	  e

      end
      else
	(let body' = pattneutEtaLong_mutable body in
	 match body'.term with
	     `LamMany(lams', body'') ->
	       assert (narrows == nlams + List.length lams') ;
	       let res = { e with term = `LamMany( lams ++ lams', body'' ) } in
	       (* let extra = PattExtras.castout e.extra in
	       let renormneed = match rng.term with `TVar(_, Some (`Meta, _), _) -> `Cached res | _ -> `Never in
	       perform
		 _ <-- Ref.setM extra.renormneed renormneed ; *)
	         res)

and pattneutEtaLong_mutable (e : pattneut) : pattcanon =

  match e.term with

    `Meta(s, idx, subst, tf) ->

      let (lamsinfo, subst', newt) = pattsubstEtaExpand_mutable subst e.classifier e.loc in
      let body = { e with term = `Meta(s, idx, subst', tf) ; classifier = newt ; extra = PattExtras.empty () } in
      pattneutUpdateMetaBoundNames_mutable body ;
      { e with term = `LamMany( lamsinfo, body ) ; extra = PattExtras.empty () }

  | `AppMany( hd, args, argsinfo ) ->

      let argsT, rangeT = gatherArrows e.classifier in
      let newones = List.length argsT in
      let (lamsinfo, args', argsinfo') = makeArgs argsT rangeT hd.loc in
      let hd = pattheadShift newones hd in
      let args = List.map (pattcanonShift newones) args in
      let args'' = args ++ args' in
      (* let args'' = List.map pattcanonEtaLong_mutable args'' in *)
      let body = { e with  term = `AppMany( hd, args'', argsinfo ++ argsinfo') ;
                           classifier = rangeT ; extra = PattExtras.empty () }
      in
      { e with term = `LamMany( lamsinfo, body ) ; extra = PattExtras.empty () }

and pattsubstEtaExpand_mutable (s : subst) (t : typ) l : ((name * typ) typinfo list * subst * typ) =

  match s with

    `Subst(args, _, argsinfo, names) ->
      
        let argsT, rangeT = gatherArrows t in
	let newones = List.length argsT in
	let (lamsinfo, args', argsinfo') = makeArgs argsT rangeT l in
	let args = List.map (pattcanonShift newones) args in
	let args'' = args ++ args' in
	let names' = List.map (function { term = (n, _) } -> n) lamsinfo in
	(* let args'' = List.map pattcanonEtaLong_mutable args'' in *)
	let subst' = `Subst(args'', None, argsinfo ++ argsinfo', names ++ names') in
	(lamsinfo, subst', rangeT)

and makeArgs (typs : typ list) (rng : typ) l
             : ((name * typ) typinfo list * pattcanon list * unit typinfo list) =

  let lamsinfo = List.map (fun info ->
      match chaseType info with
	{ term = `Arrow(t, _) } ->
	    let state = !tempstate in
            let i = state.rsmetas in
	    let s = "anon" ^ (string_of_int i) in
	    let nmeta = addRunMeta_mutable None in
	    let name = `Abstract(s, nmeta) in
	     { info with term = (name, t) ; classifier = info }
      | _ -> assert false) typs
  in
  let argsinfo, _ = getIntermediateArrows
    (List.map (fun { term = (_, t) } -> t) lamsinfo) rng rng.loc
  in
  let n = List.length typs in
  let args = List.mapi
      (fun i { term = (name,t) } ->
	pattheadToCanon { term = `Var(name, (`Bound, n-i-1)) ;
			  classifier = t ; loc = None ; extra = PattExtras.empty () })
      lamsinfo
  in
  (lamsinfo, args, argsinfo)

;;


let pattcanonRenormalize_mutable p = intermlang (fun _ -> pattcanonEtaLong_mutable ~only_top:true p) ;;
let pattneutRenormalize_mutable  p = intermlang (fun _ -> pattcanonEtaLong_mutable ~only_top:true (p |> pattneutToCanon)) ;;
let pattcanonRenormalize p = inmonad ~statewrite:true (fun _ -> intermlang (fun _ -> pattcanonEtaLong_mutable ~only_top:true p));;
let pattneutRenormalize  p = inmonad ~statewrite:true
    (fun _ -> intermlang (fun _ -> pattcanonEtaLong_mutable ~only_top:true (p |> pattneutToCanon)))
;;

(* ---- eta re-expansion ends *)


(* --------- hereditary substitutions for patterns *)

exception NeutToCanon of pattcanon ;;

let rec pattneutSubstAux curbound substbound (sigma : pattcanon Lazy.t list) (p : pattneut) : pattneut =

  match p.term with
    
    `AppMany( { term = `Var(_, (`Bound, i)) }, args, argsinfo ) when i >= curbound && i - curbound < List.length sigma ->

      let idx = i - curbound in
      let si  = List.nth sigma idx |> Lazy.force in
      let _ = assert (curbound >= substbound) in
      let si' = pattcanonShift (curbound - substbound) si in
      begin
      match si'.term with

	| `LamMany(info, body) when List.length info <= List.length args ->

	  let n = List.length info in
	  let substargs, appargs = List.split_at n args in
	  let substargsinfo, appargsinfo = List.split_at n argsinfo in
	  (* TODO missing name unification *)
	  let sigma' = List.map (fun x -> lazy(pattcanonSubstAux curbound substbound sigma x)) substargs in
	  let res = pattneutSubstAux (curbound + n) curbound sigma' body in
	  if List.length appargs <> 0 then
	    reapplyAppsPatt appargs appargsinfo res
	  else
	    res

	| `LamMany(info, body) ->
	  let n = List.length info in
	  let k = List.length args in
	  let infosubst, inforest = List.split_at k info in
	  let typ' = (List.hd inforest).classifier in
	  let sigma' = List.map (fun x -> lazy(pattcanonSubstAux curbound substbound sigma x)) args in
	  let body' = pattneutSubstAux (curbound + n) curbound sigma' body in
	  let res = { p with term = `LamMany(inforest, body') ; classifier = typ' ; extra = PattExtras.empty () } in
	  raise (NeutToCanon(res))

      end

  | `AppMany( { term = `Var(s, (`Bound, i)) } as head, args, argsinfo ) ->
      let head' = { head with term = `Var(s, (`Bound, i)) } in
      let args' = List.map (pattcanonSubstAux curbound substbound sigma) args in
      { p with term = `AppMany(head', args', argsinfo) }

  | `AppMany( { term = `Var(_, _) } as hd, args, argsinfo )
  | `AppMany( { term = `Const(_) } as hd, args, argsinfo ) ->
    let args' = List.map (pattcanonSubstAux curbound substbound sigma) args in
    { p with term = `AppMany(hd, args', argsinfo) }

  | `Meta(s,i,subst,t) ->
    
    let subst' = pattsubstSubstAux curbound substbound sigma subst in
    { p with term = `Meta(s,i,subst',t) }

and reapplyAppsPatt args argsinfo body : pattneut =

  match body.term with
    `Meta(s, i, `Subst(subst, inv, typs, names), typfull) ->

      let subst' = subst ++ args in
      let typs' = typs ++ argsinfo in
      let names' = names ++ (List.map (fun _ -> `Anon) args) in
      let typ' = (List.last argsinfo).classifier in
      let res  = { body with term = `Meta(s, i, `Subst(subst', None, typs', names'), typfull) ; classifier = typ' ; extra = PattExtras.empty () } in
      res


  | `AppMany(hd, args0, argsinfo0) ->
    let typ' = (List.last argsinfo).classifier in
    let res  = { body with term = `AppMany(hd, args0 ++ args, argsinfo0 ++ argsinfo) ; classifier = typ' ; extra = PattExtras.empty () } in
    res


and pattsubstSubstAux curbound substbound (sigma : pattcanon Lazy.t list) (s : subst) : subst = 

  match s with

    `Subst(subst, inv, info, names) ->

      let subst' = List.map (pattcanonSubstAux curbound substbound sigma) subst in
      `Subst(subst', None, info, names)

and pattcanonSubstAux curbound substbound (sigma : pattcanon Lazy.t list) (p : pattcanon) : pattcanon =

  match p.term with
    
    `LamMany(info, body) ->
      (try
	 let body' = pattneutSubstAux (curbound + List.length info) substbound sigma body in
	 { p with term = `LamMany(info, body') }
       with NeutToCanon(p') ->
	 match p'.term with
	   `LamMany(info', body') ->
	     { p with term = `LamMany(info ++ info', body') ; extra = PattExtras.empty () })

;;

let pattneutSubstMany s p =
  pattneutSubstAux 0 0 (List.map (fun x -> lazy(x)) s) p
;;
  
let pattcanonSubstMany s p = pattcanonSubstAux 0 0 (List.map (fun x -> lazy(x)) s) p ;;

(* ---- hereditary substitution ends *)


exception PattUnifyError of string ;;

(* ------ type unification stuff *)

let typUnifyBool ?(allow_instantiation = true) (t1 : typ) (t2 : typ) : bool =

  match t1.term, t2.term with

    `TVar(_, Some (`Free, idx1), []), `TVar(_, Some (`Free, idx2), []) -> idx1 == idx2
  | _ ->

  try


    if !_DEBUG then (let t1 = prepareTypeForUser t1 in
		     let t2 = prepareTypeForUser t2 in
		     Printf.printf "%a ~t~ %a\n%!" Typ.print t1 Typ.print t2);

    let typUnify ~allow_instantiation t1 t2 =
      profile "runtime typ unification"
	(lazy("typunify")) (lazy(typUnify ~allow_instantiation:allow_instantiation t1 t2))
    in

    typUnify ~allow_instantiation:allow_instantiation t1 t2 ;
    true

  with UnifyError(_,_) | OccursCheck(_, _) -> false | e -> raise e

;;


let pattcanonTypUnify ?(allow_instantiation = true) (p1 : pattcanon) (p2 : pattcanon) : unit =

  if !_DEBUG then Printf.printf "%a ~(t)~ %a\n%!" Pattcanon.print p1 Pattcanon.print p2 ;

  intermlang begin fun _ ->

  let b = typUnifyBool ~allow_instantiation:allow_instantiation p1.classifier p2.classifier in
	
  if !_DEBUG && not b then (let t1 = prepareTypeForUser p1.classifier in
			    let t2 = prepareTypeForUser p2.classifier in
			    Printf.printf " !! %a ~t %a FAILED\n%!" Typ.print t1 Typ.print t2) ;

  if not b then raise (PattUnifyError "runtime type unification")

  end

;;
    

let pattneutTypUnify ?(allow_instantiation = true) (p1 : pattneut) (p2 : pattneut) : unit =

  if !_DEBUG then Printf.printf "%a ~(t)~ %a\n%!" Pattneut.print p1 Pattneut.print p2 ;
  
  intermlang begin fun _ ->

  let b = typUnifyBool ~allow_instantiation:allow_instantiation p1.classifier p2.classifier in
	
  if !_DEBUG && not b then (let t1 = prepareTypeForUser p1.classifier in
			    let t2 = prepareTypeForUser p2.classifier in
			    Printf.printf " !! %a ~t %a FAILED\n%!" Typ.print t1 Typ.print t2) ;

  if not b then raise (PattUnifyError "runtime type unification")

  end

;;

(* ------ type unification stuff ends *)


let expandMeta subst slen p =
  let subst' = match subst with `Subst(subst,_,_,_) -> subst in
  (* let _ = assert (List.length subst' >= slen) in *)
  (* let subst' = if List.length subst' > slen then List.take slen subst' else subst' in *)
  if List.length subst' > slen then
    (let p = pattneutRenormalize_mutable p in
     match p.term with
       `LamMany(lamsinfo, body) ->
	 assert (List.length lamsinfo + slen = List.length subst');
	 let res = pattneutSubstMany (List.rev subst') body in
	 res)
  else
      (let res = pattneutSubstMany (List.rev subst') p in
      res)
;;


module PUBench = struct
  let expandMeta subst slen p		= bench "expand meta (in PU)"
                                          (lazy(expandMeta subst slen p))
  let updateMetaBoundNames_mutable i s  = bench "update meta bound (in PU)"
                                          (lazy(updateMetaBoundNames_mutable i s))
  let pattcanonRenormalize_mutable p	= bench "patt renormalize (in PU)"
                                          (lazy(pattcanonRenormalize_mutable p))
end ;;

let rec chasePattneut_mutable ?(deep = false) ?(update = false)
                  (bound : name list) (p : pattneut) : pattneut =

  (* let open PUBench in *)
  match p.term with

    `Meta(s,i,subst,typfull) -> 

      let parent = getMetaParent_mutable i in

      (match parent, subst with

	| None, `Subst([], _, _, _) -> p	  

	| None, _ ->
	  let subst' = chaseSubst_mutable ~deep:deep ~update:update bound i subst in
	  { p with term = `Meta(s, i, subst', typfull) }

	| Some (parent, slen), `Subst(s,_,_,_) ->

	  chaseAndUpdateNames ~update:update bound i subst ;

	  (*
	  let parent =
	  (* do some path compression *)
	    (match parent.term with
	    | `Meta(_, j, (`Subst(s',_,_,_) as subst'), _) when List.length s == slen ->
	      (match getMetaParent_mutable j with
	      | Some (gparent, slen') when List.length s' == slen' && slen == slen' ->
		let expanded = expandMeta subst' slen' gparent in
		setMetaParent_mutable i expanded ~substlen:slen;
		expanded
	      | _ -> parent)
	    | _ -> parent); 
	    
	  in
	  *)

	  let neut' = expandMeta subst slen parent in
	                             
	  chasePattneut_mutable ~deep:deep bound neut')

  | `AppMany( { term = `Var(n, i) } as hd, args, argsinfo ) when deep ->

    let n' = chaseName_mutable n in
    let hd' = { hd with term = `Var(n', i) } in
    let args' = List.map pattcanonRenormalize_mutable args in
    let args' = List.map (chasePattcanon_mutable ~deep:deep bound) args' in
    { p with term = `AppMany(hd', args', argsinfo) }

  | `AppMany( { term = `Const(o) } as hd, args, argsinfo ) when deep ->

    let args' = List.map pattcanonRenormalize_mutable args in
    let args' = List.map (chasePattcanon_mutable ~deep:deep bound) args' in
    { p with term = `AppMany(hd, args', argsinfo) }

  | _ -> p

and chasePattcanon_mutable ?(deep = false) ?(update = false)
                   (bound : name list) (p : pattcanon) : pattcanon =

  (* let open PUBench in *)
  match p.term with

    `LamMany(lamsinfo, body) (* when deep *) ->

      let combined = List.map
	(fun ( { term = (n, t) } as info ) ->
	  let n' = chaseName_mutable n in
	  n', { info with term = (n', t) })
	lamsinfo
      in
      let names', lamsinfo' = List.split combined in
      let body' = chasePattneut_mutable ~deep:deep ~update:update (List.rev names' ++ bound) body in
      { p with term = `LamMany(lamsinfo', body') }

and chaseSubst_mutable ?(deep = false) ?(update = false) (bound : name list) (idx : int) (subst : subst) : subst =

  (* let open PUBench in *)

  match subst with

    `Subst(s, inv, typs, names) ->
      
      let s' = List.map (chasePattcanon_mutable ~deep:deep bound) s in
      if update then updateMetaBoundNames_mutable idx s' ;
      `Subst(s', None, typs, names)

and chaseAndUpdateNames ?(update = false) (bound : name list) (idx : int) (subst : subst) : unit =

  (* let open PUBench in *)

  match subst with

    `Subst(s, inv, typs, names) ->

      let subst = List.map (chasePattcanon_mutable bound) s in
      if update then updateMetaBoundNames_mutable idx subst

;;

let chasePattneut_mutable ?(deep = false) bound p =
  let s = if deep then "pattneut chase deep" else "pattneut chase" in
  profile s
    (lazy(Printf.sprintf "chasepattneut %a" CheapPrint.neut p))
    (lazy(chasePattneut_mutable ~deep:deep ~update:true bound p))
;;

let chasePattcanon_mutable ?(deep = false) bound p =
  let s = if deep then "pattcanon chase deep" else "pattcanon chase" in
  profile s
    (lazy(Printf.sprintf "chasepattcanon %a" CheapPrint.canon p))
    (lazy(chasePattcanon_mutable ~deep:deep ~update:true bound p))
;;


let chasePattneut ?(deep = false) bound p =
  inmonad ~statewrite:true (fun _ -> chasePattneut_mutable ~deep:deep bound p) ;;

let chasePattcanon ?(deep = false) bound p =
  inmonad ~statewrite:true (fun _ -> chasePattcanon_mutable ~deep:deep bound p) ;;


let applySubstInverse (metalevel : int) (bound : name list)
                      (subst : subst)
		      (p : pattneut) : (pattneut option) =
  
  let substhere, newsinv, boundsinv =
    match subst with
      `Subst(subst, Some(newsinv, boundsinv), _, _) -> subst, newsinv, boundsinv 
    | _ -> assert false
  in
  let findAvailableBound subst boundsinv i : pattcanon option =
    
    match IMap.Exceptionless.find i boundsinv with
      | Some { term = `Var(s,(`Bound,j)) } -> Some (List.nth subst (List.length subst - j - 1))
      | Some _ -> assert false
      | None -> None

  in

  let rec auxneut bound startbound ?(istop = false) ?(nonewmetas = false) (p : pattneut) =

      let l = List.length bound - startbound in
      match p.term with
	  
	  `AppMany(hd, args, argsinfo) ->

	    let hd'	= auxhead bound startbound hd in
	    let args'	= List.map (auxcanon ~nonewmetas:nonewmetas bound startbound) args in
	    (try
	      let hd'	= Option.get hd' in
	      let args' = List.map Option.get args' in
	      Some { p with term = `AppMany(hd', args', argsinfo) ; extra = PattExtras.empty () }
	    with _ -> None)


	| `Meta(s,i,`Subst(subst',subst'inv,ts,bound'),tfull) -> 

	  let parent = getMetaParent_mutable i in
	  let metalevel' = getMetaLevel_mutable i in
	  updateMetaBoundNames_mutable i subst' ;
	  (match parent with
		 
	      Some _ ->
		   
		let p' = chasePattneut_mutable bound p in
		auxneut bound startbound ~nonewmetas:nonewmetas p'
		  
	    | None ->
	      
	      let addNew () =

		let newmetaidx = addRunMeta_mutable (Some metalevel) in
		let newtrange = p.classifier in

		let substhere = substhere |> List.map (pattcanonShift l) in
		let extendbound = match invertSubst subst' with
		                    | Some (_, boundsinv) -> List.filter_map (findAvailableBound subst' boundsinv) (decreasing l)
				    | None -> []
		in
		let substhere = substhere ++ extendbound in

		let newts = List.map (fun x -> x.classifier) substhere in
		let newtypapps, newt = getIntermediateArrows newts newtrange p.loc in

		let newmetasubst = `Subst(substhere, None, newtypapps, bound) in

		let newmeta = { term = `Meta("_"^(string_of_int newmetaidx), newmetaidx, newmetasubst, newt) ;
				classifier = newtrange ;
				loc = p.loc ; (* TODO: track loc of unification *)
				extra = PattExtras.empty () }
		in

		let substIDargs = idSubst newts bound in
		let substID = `Subst(substIDargs, None, newtypapps, bound) in
		let newmetaID = { term = `Meta("_"^(string_of_int newmetaidx), newmetaidx, substID, newt ) ;
				  classifier = newtrange ; loc = p.loc ;
				  extra = PattExtras.empty () }
		in

		addConstraint_mutable i          (`Unif(bound, p, newmeta)) ;
		addConstraint_mutable newmetaidx (`Unif(bound, p, newmeta)) ;
		setMetaMode_mutable   newmetaidx (getMetaMode_mutable i);
		let _ = if !_DEBUG then
		        Printf.printf
			  "   ~>> (%d ^ %d) %a ~ %a\n%!"
			  i newmetaidx
			  Pattneut.print p Pattneut.print newmeta
		in
		Some newmetaID

	      in

	      let subst' = ExtList.option_map (auxcanon ~nonewmetas:true bound startbound) subst' in
	      match subst', metalevel' > metalevel with

		  None, _ | _, true -> 

		    if istop || nonewmetas then None else addNew ()

		| Some subst', _ ->

		    let subst = `Subst(subst', None, ts, bound) in
		    Some { p with term = `Meta(s,i,subst,tfull) ; extra = PattExtras.empty () })

  and auxhead bound startbound (p : patthead) : patthead option =

      let l = List.length bound - startbound in
      match p.term with

	  `Var(s, (`New,i)) when i < metalevel -> Some p 

	| `Var(s,(`New,i)) -> 

	  (match IMap.Exceptionless.find i newsinv with

	      Some p' -> let p' = pattheadShift l p' in
			 Some p'

	    | None   ->  None)

	| `Var(s,(`Free,i)) -> Some p
	  
	| `Var(s,(`Bound,i)) when i < l -> Some p

	| `Var(s,(`Bound,i)) when IMap.mem (i-l) boundsinv ->
	  
	  let b  = IMap.find (i-l) boundsinv in
	  let b' = pattheadShift l b in
	  Some b'

	| `Var(s,(`Bound,i)) -> None

	| `Const(o) -> Some p

  and auxcanon ?(nonewmetas = false) bound startbound (p : pattcanon) : pattcanon option =

    let p = pattcanonRenormalize_mutable p in
    match p.term with

	`LamMany(laminfo, body) ->

	  let bound' = List.fold_left (fun bound { term = (n, _) } -> n :: bound) bound laminfo in
	  let body'  = auxneut ~nonewmetas:nonewmetas bound' startbound body in
	  match body' with
	      Some body' -> Some { p with term = `LamMany(laminfo, body') }
	    | None -> None

  in
  auxneut bound (List.length bound) ~istop:true p
;;


exception FastApplyHasMetas ;;

let fastApplyEmptySubst
    (metalevel : int) bound (p : pattneut) : bool =

  let rec auxneut bound startbound (p : pattneut) =
    
    match p.term with
      
    | `AppMany(hd,args,argsinfo) ->
      
      auxhead bound startbound hd && (List.for_all (auxcanon bound startbound) args)
	
    | `Meta(s,idx,`Subst(subst', _, ts, bound'), tfull) ->

      raise FastApplyHasMetas

    and auxhead bound startbound (p : patthead) : bool =

      let l = List.length bound - startbound in
      match p.term with

	  `Var(s,(`New,i)) -> (i < metalevel)
	| `Var(s,(`Free,i)) -> true
	| `Var(s,(`Bound,i)) -> (i < l)
	| `Const(o) -> true

    and auxcanon bound startbound (p : pattcanon) : bool =

    match p.term with

	`LamMany(laminfo, body) ->
	  let bound' = List.fold_left (fun bound { term = (n, _) } -> n :: bound) bound laminfo in
	  auxneut bound' startbound body

  in

  auxneut bound (List.length bound) p
;;



exception PattOccursCheck of int * pattneut;;
let pattOccursCheck ?(nonrigid = false) (i : int) (p : pattneut) : bool =

  let rec auxneut seen p =

    match p.term with

         `AppMany(_, args, _) -> List.for_all (auxcanon seen) args 

       | `Meta(_,j,_,_) when i == j || ISet.mem j seen -> false

       | `Meta(_,j,subst,_) ->

	   let seen' = ISet.add j seen in
	   let parent = getMetaParent_mutable j in
	   (match parent with None -> true | Some (p, _) -> auxneut seen' p) &&
	   (if nonrigid then let args = match subst with `Subst(args,_,_,_) -> args in
	                     List.for_all (auxcanon seen) args
	    else true)

  and auxcanon seen p =
    
    match p.term with
	 `LamMany(_, body) -> auxneut seen body

  in

  auxneut ISet.empty p
;;

let pattOccursCheck ?(nonrigid = false) (i : int) (p : pattneut) : bool =
  profile "pattern occurs check"
    (lazy(Printf.sprintf "occurscheck %a" CheapPrint.neut p))
    (lazy(pattOccursCheck ~nonrigid:nonrigid i p))
;;



type constraintslist = constraintT list ;;
let emptyConstraints = [] ;;
let combineConstraints c1 c2 = c1 ++ c2 ;;

let metaSolvable ?(directly = false) m : bool =

  let idx, inv = match m with (_,idx,`Subst(_,inv,_,_),_) -> idx, inv in
  if not directly && inv <> None then
    true
  else begin
    match getMetaMode_mutable idx with
    | `Free | `New -> true | _ -> false
  end
;;

let directlySolvable (p : pattneut) : bool =
  match p.term with
    `Meta(m) -> metaSolvable ~directly:true m
  | _ -> false
;;

let metaSolvable m = metaSolvable ~directly:false m ;;



let invertAndUnifyFull (_, idx1, subst1, _) bound (p1 : pattneut) (p2 : pattneut) =

  let state 		= !tempstate in
  let metalevel 	= IMap.find idx1 state.rsmeta_level in
  let _ 		= if not (pattOccursCheck ~nonrigid:false idx1 p2) then raise (PattUnifyError("occurs check")) in
  let state 		= !tempstate in

  let applySubstInverse = fun metalevel bound subst1 p2 ->
                          log (lazy(Printf.sprintf "applysubstinv"))
                              (lazy(applySubstInverse metalevel bound subst1 p2))
  in

  let p' 		= applySubstInverse metalevel bound subst1 p2 in

  let state' 		= !tempstate in
  let p' 		= (match p' with
                            | Some p' -> p'
			    | None -> let s = Printf.sprintf "failed to invert %a over s-1 = %a"
					      Pattneut.print p2 (List.print Pattcanon.print)
					      (let `Subst(x,_,_,_) = subst1 in x)
				      in
				      raise (PattUnifyError(s)))
  in
  let slen 		= match subst1 with `Subst(s, _, _, _) -> List.length s in
  let _                 = if !_DEBUG then Printf.printf "   ~ %a ~ %a -->\n   ~= %a := %a\n%!"
	                     Pattneut.print p1
                    	     Pattneut.print p2
	                     Pattneut.print p1
	                     Pattneut.print p'
  in

  let _ 		= setMetaParent_mutable idx1 p' ~substlen:slen in
  let constraints 	= getConstraints_mutable idx1 in
  let newmetas 		= state'.rsmetas - state.rsmetas in
  let restconstraints 	= increasing newmetas
                          |> List.map (fun x -> let n = x + state.rsmetas in n, getConstraints_mutable n)
  in
  let shouldhandlenow c = match c with
                           | `Unif(_, { term = `Meta(m1) }, { term = `Meta(m2) })
			   | `UnifCanon(_,
					{ term = `LamMany([], { term = `Meta(m1) } ) },
					{ term = `LamMany([], { term = `Meta(m2) } ) }) ->
			     Option.is_some (invertSubst (metasubstmain m1)) ||
			     Option.is_some (invertSubst (metasubstmain m2))
			   | _ -> false
  in
  let restconstpart     = restconstraints |> List.map (fun (n, cs) -> n, List.partition shouldhandlenow cs) in
  let hnow              = restconstpart |> List.map (fun (n, (hnow, hlater)) -> hnow) |> List.flatten in

  List.iter (fun (n, (hnow, hlater)) -> setConstraints_mutable n hlater) restconstpart ;
  constraints ++ hnow

;;

let unifyDirectly (_, idx1, subst1, _) (p1 : pattneut) (p2 : pattneut) =

  let p' 	  = p2 in
  let _ 	  = if !_DEBUG then Printf.printf "   ~ %a ~ %a -->\n   ~= %a :=F %a\n%!"
                                    Pattneut.print p1 Pattneut.print p2
				    Pattneut.print p1 Pattneut.print p'
  in
  let slen 	  = match subst1 with `Subst(s, _, _, _) -> List.length s in
  let _ 	  = setMetaParent_mutable idx1 p' ~substlen:slen in
  let constraints = getConstraints_mutable idx1 in
  constraints

;;

let invertAndUnify ((_, idx1, subst1, _) as m) bound (p1 : pattneut) (p2 : pattneut) =

  let metalevel = getMetaLevel_mutable idx1 in
  let curmetalevel = List.length (!tempenv).renvars in
  match subst1, p2.term, curmetalevel == metalevel with

    `Subst([], _, _, _), _, true when List.is_empty bound ->

      if not (pattOccursCheck ~nonrigid:false idx1 p2) then raise (PattUnifyError("occurs check")) ;
      unifyDirectly m p1 p2

  | `Subst([], _, _, _), `AppMany(_, args, _), _ ->
      
      (try
	 let isOK = fastApplyEmptySubst metalevel bound p2 in
	 if isOK then unifyDirectly m p1 p2
	 else (raise (PattUnifyError "failed to invert"))
       with FastApplyHasMetas -> invertAndUnifyFull m bound p1 p2)

  | _ -> invertAndUnifyFull m bound p1 p2

;;



let chasedPattUnify_mutable (bound : name list) (p1 : pattneut) (p2 : pattneut) : constraintslist =

  let mzero s =
    if !_DEBUG then
      (Printf.printf "   ~ %a ~ %a -->\n   ~= FAILURE %s\n%!"
	 Pattneut.print p1 Pattneut.print p2 s);
    raise (PattUnifyError s)
  in

  let metaIdSubst (_, idx, `Subst(subst, _, _, _), _) =
    let bound =
	try IMap.find idx !tempstate.rsmeta_boundnames
	with Not_found -> bound
    in
    let typs  = List.map (fun t -> t.classifier) subst in
    idSubst typs bound
  in

  let matchMode m lvl (p : patthead) =
    match m, p.term with
      `Free, `Var(_, (`Free, _)) -> ()
    | `New,  `Var(_, (`New, i)) when i < lvl -> ()
    | _ -> mzero "did not match free/new var"
  in

  let invertAndUnify m bound p1 p2 =
    profile "invert and unify"
      (lazy(Printf.sprintf "invertunif %a" CheapPrint.neut p2))
      (lazy(invertAndUnify m bound p1 p2))
  in


  let ds1 = directlySolvable p1 in
  let ds2 = directlySolvable p2 in

  match ds1, ds2, p1, p2 with

    (* unification of imitation variables *)
    
    | true, _, { term = `Meta(_, idx1, _, _) }, { term = `Meta(_, idx2, _, _) } when idx1 == idx2 ->

      emptyConstraints

    | true, false, ({ term = `Meta(m1) } as p1), ({ term = `Meta((_, _, `Subst(_, Some _, _, _), _) as m2) } as p2)
    | false, true, ({ term = `Meta((_, _, `Subst(_, Some _, _, _), _) as m2) } as p2), ({ term = `Meta(m1) } as p1)
      ->

      invertAndUnify m2 bound p2 p1

    | true, false, { term = `Meta(m1) }, { term = `Meta(m2) }
    | false, true, { term = `Meta(m2) }, { term = `Meta(m1) } ->

      addConstraint_mutable (metaindex m1) (`Unif(bound,p1,p2)) ;
      addConstraint_mutable (metaindex m2) (`Unif(bound,p1,p2)) ;
      []

    | true, true, { term = `Meta(m1) }, { term = `Meta(m2) } ->

      if List.length (metasubstmain m1) <> List.length (metasubstmain m2) then mzero "different subst len" ;

      let m1mode = getMetaMode_mutable  (metaindex m1) in
      let m1lvl  = getMetaLevel_mutable (metaindex m1) in
      let m2mode = getMetaMode_mutable  (metaindex m2) in
      let m2lvl  = getMetaLevel_mutable (metaindex m2) in

      if m1mode <> m2mode then mzero "different modes" ;

      let m1, m2, p1, p2 =
	if m1lvl < m2lvl then m2, m1, p2, p1
	else m1, m2, p1, p2
      in

      let idsubst = metaIdSubst m2 in
      let par =

	  match p2 with

	    { term = `Meta(s, idx, `Subst(_, _, typapps, bound), typfull) } ->

	      let substnew = `Subst(idsubst, None, typapps, bound) in
	      { p2 with term = `Meta(s, idx, substnew, typfull) ; extra = PattExtras.empty () }

	  | _ -> assert false
      
      in
      
      setMetaParent_mutable (metaindex m1) par ~substlen:(List.length (metasubstmain m1)) ;

      let _ = if !_DEBUG then Printf.printf "   ~ %a ~imit~ %a --!>\n   ~= %a := %a\n%!"
	  Pattneut.print p1 Pattneut.print p2 Pattneut.print p1 Pattneut.print par
      in

      let cs = List.map2 (fun a b -> `UnifCanon(bound, a, b)) (metasubstmain m1) (metasubstmain m2) in
      let c1 = getConstraints_mutable (metaindex m1) in
      cs ++ c1

    | true, _, { term = `Meta( (_, idx1, `Subst(subst1, _, typapps, _), _) as m1 ) }, _ ->

      let idsubst = metaIdSubst m1 in
      let (hd, args, argsinfo) =
	  match p2.term with `AppMany(hd, args, argsinfo) -> hd, args, argsinfo
	  | _ -> assert false
      in
      let m1mode = getMetaMode_mutable idx1 in
      let m1lvl  = getMetaLevel_mutable idx1 in
      
      matchMode m1mode m1lvl hd ;
      if List.length idsubst <> List.length args then mzero "different subst len" ;

      let par : pattneut = { p2 with term = `AppMany(hd, idsubst, typapps) ; extra = PattExtras.empty () } in
      setMetaParent_mutable idx1 par ~substlen:(List.length subst1) ;

      let _ = if !_DEBUG then Printf.printf "   ~ %a ~imit~ %a --!>\n   ~= %a := %a\n%!"
	  Pattneut.print p1 Pattneut.print p2 Pattneut.print p1 Pattneut.print par
      in

      let cs = List.map2 (fun a b -> `UnifCanon(bound, a, b)) subst1 args in
      let c1 = getConstraints_mutable idx1 in
      cs ++ c1

    | _, true, _, _ -> failwith "should not happen"

    (* higher-order pattern matching *)

    | _, _, { term = `Meta( (_, idx1, `Subst(_, Some _, _, _), _) as m1) },
            { term = `Meta( (_, idx2, `Subst(_, Some _, _, _), _) as m2) }
	      when idx1 == idx2 ->

      let intersect = intersectSubst (metasubstmain m1) (metasubstmain m2) in
      if List.length intersect = List.length (metasubstmain m1) then []
      else begin

	let metalevel 	     = getMetaLevel_mutable (metaindex m1) in
	let newmetaidx 	     = addRunMeta_mutable (Some metalevel) in
	let newtrange 	     = p1.classifier in
	let newts 	     = List.map (fun x -> x.classifier) intersect in
	(* TODO locs here are invented *)
	let newtypapps, newt = getIntermediateArrows newts newtrange p1.loc in
	let intersectsubst   = `Subst(intersect, None, newtypapps, bound) in
	let newmeta 	     = { term = `Meta("_"^(string_of_int newmetaidx), newmetaidx, intersectsubst, newt) ;
				 classifier = newtrange ; loc = p1.loc ; extra = PattExtras.empty () }
	in
	let _ 		     = if !_DEBUG then Printf.printf "   ~ %a ~ %a --!>\n   ~= %a := %a\n%!"
	                       Pattneut.print p1 Pattneut.print p2 Pattneut.print p1 Pattneut.print newmeta
	in
	
	setMetaParent_mutable (metaindex m1) newmeta ~substlen:(List.length (metasubstmain m1)) ;
	getConstraints_mutable (metaindex m1)

      end

    | _, _, { term = `Meta( (_, _, `Subst(_, Some _, _, _), _) as m1) }, _ ->

        invertAndUnify m1 bound p1 p2

    | _, _, { term = `Meta(m1) }, _ ->

      addConstraint_mutable (metaindex m1) (`Unif(bound, p1, p2)) ;
      if !_DEBUG then Printf.printf "   ~>> %d %a ~ %a\n%!" (metaindex m1) Pattneut.print p1 Pattneut.print p2 ;
      []

    | _ -> mzero "should not happen"
;;


let chasedPattUnify_mutable bound p1 p2 =
  log (lazy(Printf.sprintf "chasedpattunify %a %a" CheapPrint.neut p1 CheapPrint.neut p2))
      (lazy(chasedPattUnify_mutable bound p1 p2))
;;


let chasedPattUnify bound p1 p2 =
  let open RunCtx.Monad in
  perform
    res <-- inmonad ~statewrite:true (fun _ -> try Some (chasedPattUnify_mutable bound p1 p2) with PattUnifyError _ -> None) ;
    match res with
    | Some cs -> return cs
    | None -> mzero
;;

(* Fast-failure for unification between p1 and p2. Compares free variables
   at the same positions up to a certain depth. 
   
   The chase1 and chase2 labels control whether we are allowed to chase
   metavariables in the first and second patterns. *)

let fastFailUnify_mutable ?(chase1 = false) (p1 : pattneut) ?(chase2 = false) (p2 : pattneut) : unit =

  let max_depth = 3 in
  let state = !tempstate in

  let rec roughChase (p : pattneut) : pattneut =

       let rec metachase p idx =
	 match IMap.Exceptionless.find idx state.rsmeta_parent with
	    Some ({ term = `Meta(_, idx', _, _) }, _) -> metachase p idx'
	  | Some ({ term = `AppMany( { term = `Var(_, (`Free, _)) }, _, _ ) } as p', _) -> p'
	  | Some ({ term = `AppMany( { term = `Var(_, (`New, _)) }, _, _ ) } as p', _)  -> p'
	  | Some ({ term = `AppMany( { term = `Const(o1) }, _, _) } as p', _) -> p'
	  | _ -> p
       in

       match p.term with
	 `Meta(_, idx, _, _) -> metachase p idx
       | _ -> p
	 
  in
  
  let rec fastFailUnify depth (p1 : pattneut) (p2 : pattneut) : bool =

       let p1 = if chase1 then roughChase p1 else p1 in
       let p2 = if chase2 then roughChase p2 else p2 in
       match p1.term, p2.term with

       | `AppMany({ term = `Var(_, (`Free, idx1)) }, _, _), `AppMany({ term = `Var(_, (`Free, idx2)) }, _, _) 
       | `AppMany({ term = `Var(_, (`New, idx1))  }, _, _), `AppMany({ term = `Var(_, (`New, idx2))  }, _, _)
	 when idx1 <> idx2 ->

	 false

       | `AppMany({ term = `Var(_, (`Free, _)) }, _, _), `AppMany({ term = `Var(_, (`New, _))  }, _, _) 
       | `AppMany({ term = `Var(_, (`New, _))  }, _, _), `AppMany({ term = `Var(_, (`Free, _)) }, _, _) ->

	 false

       | `AppMany({ term = `Const(o1) }, _, _), `AppMany({ term = `Const(o2) }, _, _) ->

	 let t1 = intermlang (chaseTypeDeep p1.classifier) in
	 let t2 = intermlang (chaseTypeDeep p2.classifier) in
	 Const.eq o1 o2 { p1 with term = `Const(o1) ; classifier = t1 }
		        { p2 with term = `Const(o2) ; classifier = t2 }

       | `AppMany({ term = `Var(_, (`Free, _)) }, args1, _), `AppMany({ term = `Var(_, (`Free, _)) }, args2, _)
       | `AppMany({ term = `Var(_, (`New, _))  }, args1, _), `AppMany({ term = `Var(_, (`New, _))  }, args2, _)
	 when depth < max_depth && List.length args1 == List.length args2 ->

	 let canon p1 p2 = 
	   
	   match p1.term, p2.term with
	     
	     `LamMany([], body1), `LamMany([], body2) ->
	       
	       fastFailUnify (depth+1) body1 body2
		 
	   | _ -> true
	     
	 in
	 List.for_all2 canon args1 args2

       | _ -> true

  in
  if not (fastFailUnify 0 p1 p2) then raise (PattUnifyError "fastfail")

;;


(* Entry point for pattern unification. *)

let pattUnify_mutable, pattUnifyCanon_mutable =

  let abstractNamesAllowedFor idx = 
    match idx with `Bound, _ | `New, _ -> true | _ -> false
  in

  let nameUnifyLams { term = (n1,_) } { term =  (n2,_) } = nameUnify_mutable n1 n2 in
	
  let rec pattUnify (bound : name list) (p1 : pattneut) (p2 : pattneut) : constraintT list =

    if !_DEBUG then Printf.printf "%a ~~ %a\n%!" Pattneut.print p1 Pattneut.print p2;

    (*
    pattneutTypUnify p1 p2 ;

    let p1' = chasePattneut_mutable bound p1 in
    let p2' = chasePattneut_mutable bound p2 in

    if !_DEBUG then Printf.printf "%a ~(chased)~ %a\n%!" Pattneut.print p1' Pattneut.print p2' ;
    *)

    let p1' = invertSubstNeut p1 in
    let p2' = invertSubstNeut p2 in
      
    match p1'.term, p2'.term with

      | `AppMany(head1, args1, _), `AppMany(head2, args2, _) ->

	pattUnifyHead head1 head2 ;
	let cs = List.map2 (pattUnifyCanon bound) args1 args2 in
	List.flatten cs
	  
      | `Meta(m1), `Meta(m2) ->

	begin
	match metaSolvable m1, metaSolvable m2 with

	  | true, true ->
	
	    let l1 = getMetaLevel_mutable (metaindex m1) in
	    let l2 = getMetaLevel_mutable (metaindex m2) in
	    let (pa, pb) = if l1 > l2 then p1', p2' else p2', p1' in

	    (try
	       
	       chasedPattUnify_mutable bound pa pb

	     with PattUnifyError _ ->

	       addConstraint_mutable (metaindex m1) (`Unif(bound, p1', p2')) ;
	       addConstraint_mutable (metaindex m2) (`Unif(bound, p1', p2')) ;
	       if !_DEBUG then Printf.printf "   ~>> (%d,%d) %a ~ %a\n%!"
		               (metaindex m1) (metaindex m2) Pattneut.print p1' Pattneut.print p2';
	       [])

	  | false, true -> chasedPattUnify_mutable bound p2' p1'
	  | _ -> chasedPattUnify_mutable bound p1' p2'

	end

      | (`Meta(m1)), _ -> chasedPattUnify_mutable bound p1' p2'

      | _, (`Meta(m2)) -> chasedPattUnify_mutable bound p2' p1'

  and pattUnifyHead (p1 : patthead) (p2 : patthead) =

    match p1.term, p2.term with

    | (`Var(n1, i1)), (`Var(n2, i2)) ->

      if i1 <> i2 then begin

	if !_DEBUG then Printf.printf "%a ~! %a FAILED\n" Patthead.print p1 Patthead.print p2 ;
        raise (PattUnifyError "head mismatch")

      end
      else if abstractNamesAllowedFor i1 && abstractNamesAllowedFor i2
      then ignore(nameUnify_mutable n1 n2)

    | (`Const(o1)), (`Const(o2)) ->
      
      let t1 = intermlang (chaseTypeDeep p1.classifier) in
      let t2 = intermlang (chaseTypeDeep p2.classifier) in

      if not (Const.eq o1 o2 { p1 with term = `Const(o1) ; classifier = t1 }
		             { p2 with term = `Const(o2) ; classifier = t2 })
      then raise (PattUnifyError "const mismatch")

    | _ -> raise (PattUnifyError "head mismatch")

  and pattUnifyCanon (bound : name list) (p1 : pattcanon) (p2 : pattcanon) =

      if !_DEBUG then Printf.printf "%a ~C~ %a\n%!" Pattcanon.print p1 Pattcanon.print p2 ;

      pattcanonTypUnify p1 p2 ;

      let p1' = pattcanonRenormalize_mutable p1 in
      let p1' = chasePattcanon_mutable bound p1' in
      let p2' = pattcanonRenormalize_mutable p2 in
      let p2' = chasePattcanon_mutable bound p2' in

      if !_DEBUG then Printf.printf "%a ~(Cchased)~ %a\n%!" Pattcanon.print p1' Pattcanon.print p2' ;

      match p1'.term, p2'.term with

	`LamMany(lams1, body1), `LamMany(lams2, body2) ->

	  (* let _ = assert (List.length lams1 == List.length lams2) in *)
	  let ns = List.map2 nameUnifyLams lams1 lams2 in
	  let bound = List.rev ns ++ bound in
	  pattUnify bound body1 body2 
	
  in

  let pattUnify ?(bound = []) (p1 : pattneut) (p2 : pattneut) : (constraintT list) =
    pattUnify bound p1 p2
  in
  let pattUnifyCanon ?(bound = []) (p1 : pattcanon) (p2 : pattcanon) : (constraintT list) =
    pattUnifyCanon bound p1 p2
  in

  pattUnify, pattUnifyCanon

;;

let pattUnify ?(bound = []) (p1 : pattneut) (p2 : pattneut) : (constraintT list) RunCtx.Monad.m =
  let open RunCtx.Monad in
  perform
    res <-- inmonad ~statewrite:true (fun _ -> try Some (pattUnify_mutable ~bound:bound p1 p2) with PattUnifyError _ -> None) ;
    match res with
      | Some res -> return res
      | None -> mzero
;;

let pattUnifyCanon ?(bound = []) (p1 : pattcanon) (p2 : pattcanon) : (constraintT list) RunCtx.Monad.m =
  let open RunCtx.Monad in
  perform
    res <-- inmonad ~statewrite:true (fun _ -> try Some (pattUnifyCanon_mutable ~bound:bound p1 p2) with PattUnifyError _ -> None) ;
    match res with
      | Some res -> return res
      | None -> mzero
;;


(* Entry point for pattern unification; extra constraints handled in a depth-first manner. *)

let rec pattUnifyFull_mutable ?(bound = []) p1 p2 =

  let cs = pattUnifyCanon_mutable ~bound:bound (pattneutToCanon p1) (pattneutToCanon p2) in
  List.iter handleConstraint_mutable cs

and pattcanonUnifyFull_mutable ?(bound = []) p1 p2 =

  let cs = pattUnifyCanon_mutable ~bound:bound p1 p2 in
  List.iter handleConstraint_mutable cs

and handleConstraint_mutable c =

  match c with
    `Unif(bound,p1,p2) -> pattUnifyFull_mutable ~bound:bound p1 p2
  | `UnifCanon(bound,p1,p2) -> pattcanonUnifyFull_mutable ~bound:bound p1 p2
  | (`Demand(idx,_,p,env) as demand) -> 
    let isconcrete = 
     (match getMetaParent_mutable idx with
	 Some (p, _) ->
	   (match (chasePattneut_mutable [] p).term with
	       `Meta(_) -> false
	     | _ -> true)
       | _ -> true)
    in
    if isconcrete then addOpenGoal_mutable p env else addConstraint_mutable idx demand
  | `RemoveDemand(fromidx,whichidx) ->
    let cs = getConstraints_mutable fromidx in
    let cs' = List.filter (function `Demand(_,Some whichidx',_,_) when whichidx == whichidx' -> false | _ -> true) cs in
    setConstraints_mutable fromidx cs'

;;

let pattunifytimer = "pattern unification" ;;

let pattUnifyFull_mutable ?(bound = []) p1 p2 = 
  profile pattunifytimer
      (lazy(Printf.sprintf "pattunify %a %a" CheapPrint.neut p1 CheapPrint.neut p2))
      (lazy(pattUnifyFull_mutable ~bound:bound p1 p2))
;;

let pattcanonUnifyFull_mutable ?(bound = []) p1 p2 = 
  profile pattunifytimer
      (lazy(Printf.sprintf "pattcanonunify %a %a" CheapPrint.canon p1 CheapPrint.canon p2))
      (lazy(pattcanonUnifyFull_mutable ~bound:bound p1 p2))
;;


let pattUnifyFull ?(bound = []) p1 p2 =
  let open RunCtx.Monad in
  perform
    res <-- inmonad ~statewrite:true (fun _ -> try Some (pattUnifyFull_mutable ~bound:bound p1 p2) with PattUnifyError _ -> None) ;
    match res with
      | Some res -> return res
      | None -> mzero
;;  

let pattcanonUnifyFull ?(bound = []) p1 p2 =
  let open RunCtx.Monad in
  perform
    res <-- inmonad ~statewrite:true (fun _ -> try Some (pattcanonUnifyFull_mutable ~bound:bound p1 p2) with PattUnifyError _ -> None) ;
    match res with
      | Some res -> return res
      | None -> mzero
;;  



(* reconstruct lambda abstractions for metavariables *)
let reconstructLambdas (t : typ) (boundnames : name list) (p : pattneut) : pattcanon =

  match (chaseType t).term with 
    `Arrow(_,_) ->
      (let typs, rng = gatherArrows t in
       let ntyps = List.length typs in
       let nnames = List.length boundnames in
       let boundnames =
	 if nnames < ntyps then boundnames ++ (List.make (ntyps - nnames) `Anon)
	 else if nnames > ntyps then List.take ntyps boundnames
	 else boundnames
       in
       let comb = List.combine boundnames typs in
       let lamsinfo =
	 List.map
	   (fun (name, typ) -> 
	     match (chaseType typ).term with
	       `Arrow(dom,_) -> { p with term = (name, dom) ; classifier = typ }
	     | _ -> assert false)
	   comb
       in
       let body = { p with classifier = rng ; extra = PattExtras.empty () } in
       let overalltyp = (List.hd lamsinfo).classifier in
       { p with term = `LamMany(lamsinfo, body) ; classifier = overalltyp ; extra = PattExtras.empty () })

  | _ -> { p with term = `LamMany([], p) ; extra = PattExtras.empty () }

;;

(* ------------ typing : check clauses and queries --- *)

exception UnknownPredicate of pattneut ;;
exception MalformedClause  of pattneut ;;
exception MalformedClauseTypecase  of pattneut * typ * typ ;;
exception ClauseForBuiltin of pattneut * string ;;

let builtin_predicates : (typ -> pattcanon list -> unit RunCtx.Monad.m) IMap.t ref = ref IMap.empty ;;

let headPredicate (p : pattneut) =
  match p.term with
      `AppMany( { term = `Var(_, (`Free, idx')) }, _, _) -> idx'
    | p' -> raise (UnknownPredicate(p))
;;

let getInfoFromClause (p : pattneut) =
  match p.term with
    | `AppMany( { term = `Var(_, (`Free, idx)) },
	      [ { term = `LamMany([], goal) } ; { term = `LamMany([], premise) } ], _) when idx = _eiClause ->
      let idx' = headPredicate goal in
      (idx', goal, None, premise)

    | `AppMany( { term = `Var(_, (`Free, idx)) },
	      [ { term = `LamMany([], goal) } ; { term = `LamMany([], cond) } ; { term = `LamMany([], premise) } ], _)
	when idx = _eiWhenClause ->
      let idx' = headPredicate goal in
      (idx', goal, Some cond, premise)
	
    | _ -> raise (MalformedClause(p))
;;

let getInfoFromUnchasedClause_mutable (p : pattneut) =
  match p.term with
    `AppMany( { term = `Var(_, (`Free, idx)) } as hd,
	      [ { term = `LamMany([], goal) } as gl ;
		{ term = `LamMany([], premise) } as pr ], argsinfo) when idx = _eiClause ->

      let goal = chasePattneut_mutable [] goal in
      let idx' = headPredicate goal in
      let clause' = { p with term = `AppMany(hd,
					     [ { gl with term = `LamMany([], goal) } ; pr],
					     argsinfo) }
      in
      idx', goal, None, premise, clause'

  | `AppMany( { term = `Var(_, (`Free, idx)) } as hd,
	      [ { term = `LamMany([], goal) } as gl ;
		{ term = `LamMany([], cond) }  as cd ;
		{ term = `LamMany([], premise) } as pr ], argsinfo) when idx = _eiWhenClause ->

      let goal = chasePattneut_mutable [] goal in
      let idx' = headPredicate goal in
      let clause' = { p with term = `AppMany(hd,
					     [ { gl with term = `LamMany([], goal) } ; cd; pr],
					     argsinfo) }
      in
      idx', goal, Some cond, premise, clause'

  | _ -> raise (MalformedClause(p))
;;


(* tracing check *)
let isTraced_mutable goalidx =
  let state = !tempstate in
  ISet.mem goalidx state.rstraced_predicates
;;

let setTracedIndex_mutable shouldbetraced goalidx =
  let state = !tempstate in
  let istraced = ISet.mem goalidx state.rstraced_predicates in
  let modifyfunc =
    match istraced, shouldbetraced with
      | true, true -> (fun x -> x)
      | true, false -> ISet.remove goalidx
      | false, true -> ISet.add goalidx
      | false, false -> (fun x -> x)
  in
  tempstate := { state with rstraced_predicates = modifyfunc state.rstraced_predicates }
;;

let setTraced_mutable shouldbetraced p =
  let p = pattneutRenormalize_mutable p in
  let goalidx = 
    match p.term with
	`LamMany(_, p') -> headPredicate p'
  in
  setTracedIndex_mutable shouldbetraced goalidx
;;

let setTraced shouldbetraced p =
  let open RunCtx.Monad in
  inmonad ~statewrite:true (fun _ -> setTraced_mutable shouldbetraced p)
;;

let setTracedIndex shouldbetraced idx =
  let open RunCtx.Monad in
  inmonad ~statewrite:true (fun _ -> setTracedIndex_mutable shouldbetraced idx)
;;


let shiftTMetas addtmetas t =
  let rec taux t = 
    match t.term with
      `Arrow(t1, t2) -> { t with term = `Arrow(taux t1, taux t2) }
    | `TVar(name, Some(`Meta, i), args) -> { t with term = `TVar(name, Some(`Meta, i+addtmetas), args) }
    | `TVar(name, idx, args) -> { t with term = `TVar(name, idx, List.map taux args) }
    | _ -> assert false
  in
  taux t
;;

  (* Check that the goal does not specialize type variables.
     E.g. for the predicate test : A -> prop,
     the clause: clause (test "hello") success
     should not be allowed. 
     Works by instantiating polymorphic variables in the signature of the predicate
     with new free type variables,
     and then checking type unification between the inferred type of the goal and
     this expected type. Any specialization will make unification fail.
     This way we disallow typecase-like things, and avoid the need of typechecking during
     runtime proof search.
     ----------- Note that for the time being I'm not using this.
  *)
let checkWellformedClause e goalpatt =

  let origstate = !termstate in
  let goal = match gatherApps e with (_, (goal :: _), _) -> goal | _ -> assert false in
  let goalhd, idx = match gatherApps goal with
    | { term = `Var(_, (`Free, idx))} as goalhd, _, _ -> goalhd, idx
    | _ -> assert false
  in

  let typ_actual   = goalhd.classifier in

  let polytyp      = lookupFVarPolytyp idx in
  let typ_expected = instantiateWithTFvars polytyp in

  let state        = !termstate in
  let b            = typUnifyBool typ_actual typ_expected in
  
  termstate := state ;

  if b then termstate := origstate else
    (let texp = prepareTypeForUser typ_expected in
     let tact = prepareTypeForUser typ_actual in
     termstate := origstate ;
     raise (MalformedClauseTypecase(goalpatt, texp, tact)))

;;	
      
       
let exprToProp ((e, nameunifs) : expr * nameunifs) : prop =

  let e' = chaseTypesInExpr ~replaceUninst:true e in
  let p  = exprToPatt e' in
  let state = !termstate in
  let metas  = state.metas in
  let tmetas = state.polytmetas in
  { patt = p ; propmetas = metas ; proptmetas = tmetas ; propnameunifs = nameunifs ; prophasrunmetas = false }

;;


let checkClauseNotBuiltin p idx =

  let name = nameOfFVar idx in
  if IMap.mem idx !builtin_predicates then raise (ClauseForBuiltin(p,name))

;;

let checkClause (e : exprU) : int * prop =

  let e 		    = { e with term = `Annot(e, _tClause) ; classifier = _tClause } in
  let (e', _) as res        = typecheck_and_normalize e in
  let pr 		    = exprToProp res in
  let (idx, pattgoal, _, _) = getInfoFromClause pr.patt in

  checkClauseNotBuiltin pr.patt idx ;
  checkWellformedClause e' pattgoal ;
  idx, pr

;;

let checkQuery (e : exprU) =

  let e   = { e with term = `Annot(e, _tProp) ; classifier = _tProp } in
  let res = withConcreteBoundMode true (fun _ -> typecheck_and_normalize e) in
  exprToProp res

;;


(* ------------ runtime : solving a goal --------- *)
let shiftMetasName addmetas n : name =
  match n with
      `Abstract(s,i) -> `Abstract(s, i+addmetas)
    | _ -> n
;;

let shiftMetasTyp addtmetas t =
  let rec taux t =
    match t.term with
      `Arrow(t1, t2) -> { t with term = `Arrow(taux t1, taux t2) }
    | `TVar(name, Some(`Meta, i), args) ->
      assert (args = []) ;
      { t with term = `TVar(name, Some(`Meta, i+addtmetas), args) }
    | `TVar(name, idx, args) ->
      { t with term = `TVar(name, idx, List.map taux args) }
    | _ -> assert false
  in
  let t = taux t in
  { t with extra = TypExtras.empty () }
;;


let shiftMetas addmetas addtmetas pr : pattneut =
  let rec auxneut p = 
    let p = { p with classifier = taux p.classifier ; extra = PattExtras.empty () } in
    match p.term with
        `AppMany(head, args, argsinfo) -> 
	  let head' = auxhead head in
	  let args' = List.map auxcanon args in
	  let argsinfo' = List.map tinfoaux argsinfo in
	  { p with term = `AppMany(head', args', argsinfo') }
      | `Meta(s,i,`Subst(subst,substinv,ts,bound),t) ->
	let ts' = List.map tinfoaux ts in
	let substinv' = Option.map (Pair.map (IMap.map auxhead)) substinv in
	let subst' = List.map auxcanon subst in
	let bound' = List.map naux bound in
	{ p with term = `Meta(s,i+addmetas,`Subst(subst',substinv',ts',bound'),taux t) }
  and auxhead p =
    let p = { p with classifier = taux p.classifier ; extra = PattExtras.empty () } in
    match p.term with
        `Var(s,i)      -> { p with term = `Var(naux s, i) }
      | _ -> p
  and auxcanon p =
    let p = { p with classifier = taux p.classifier ; extra = PattExtras.empty () } in
    match p.term with
      `LamMany(lamsinfo, body) ->
	let lamsinfo' = List.map (fun ( { term = (n, tdom) ; classifier = t } as info ) ->
	  { info with term = (naux n, taux tdom) ; classifier = taux t }) lamsinfo
	in
	let body' = auxneut body in
	{ p with term = `LamMany(lamsinfo', body') }
  and naux n = shiftMetasName addmetas n
  and taux t = shiftMetasTyp addtmetas t
  and tinfoaux t = { t with classifier = taux t.classifier }
  in
  auxneut pr
;;

let shiftMetasNameunifs addmetas nu : nameunifs =
  let naux = shiftMetasName addmetas in 
  List.map (Pair.map naux) nu
;;

let allocateMetas_mutable (pr : prop) : (pattneut * nameunifs) =
  intermlang (fun _ ->
  if pr.propmetas > 0 || pr.proptmetas > 0 then begin
    let state = !tempstate in
    List.iter (fun _ -> ignore(addRunMeta_mutable None)) (increasing pr.propmetas) ;
    (* note that we do not allocate metas in the term language, only type-metas.
       so typing terms would not really work *)
    List.iter (fun _ -> ignore(newTMeta pr.patt.loc)) (increasing pr.proptmetas) ;
    let p = shiftMetas state.rsmetas state.rstermstate.tmetas pr.patt in
    pattneutUpdateMetaBoundNames_mutable p ;
    let nu = shiftMetasNameunifs state.rsmetas pr.propnameunifs in
    p, nu
  end else (pr.patt, pr.propnameunifs))
;;


let allocateFvar s t =
  let open RunCtx.Monad in
  perform
      env <-- getenv ;
      let env' = { env with renvars = env.renvars ++ [s,t] } in
      return env'
;;


let findConstructors pred =
  let open RunCtx.Monad in
  perform
    state <-- getstate ;
    env   <-- getenv   ;
    let normal = try IMap.find pred state.rsconstr_for_pred with Not_found -> [] in
    let temp   = try IMap.find pred env.retemp_constr_for_pred with Not_found -> [] in
    return (temp ++ normal)
;;

let addTempConstructor idx p =

  let open RunCtx.Monad in
  let newconstr = { patt = p ; propmetas = 0 ; proptmetas = 0 ; propnameunifs = [] ; prophasrunmetas = true } in
  perform
    env <-- getenv ;
    return { env with retemp_constr_for_pred =
	                 IMap.modify_def [] idx (fun l -> newconstr :: l)
			 env.retemp_constr_for_pred }
;;

let resetTempConstructors idx =
  
  let open RunCtx.Monad in
  perform
    env <-- getenv ;
    return { env with retemp_constr_for_pred = IMap.modify_def [] idx (fun _ -> [])
	                                       env.retemp_constr_for_pred }
;;


let rec _demandNormal (newgoal : pattneut) : unit RunCtx.Monad.m =

  let open RunCtx.Monad in

  let debugEnter pred = 
    if !_DEBUG then
      perform
	  let _ = if !_DEBUG then Printf.printf "*** %a\n%!" Pattneut.print newgoal in
	  chased <-- chasePattneut ~deep:true [] newgoal ;
	  let _ = Printf.printf " *= %a\n%!" Pattneut.print chased in
	  return ()
    else
      return ()
  in
  let debugFailAppend initstate pred x =
    if !_DEBUG then
      List.append x
	[lazy(perform
	    _ <-- setstate initstate ;
	    chased <-- chasePattneut ~deep:true [] newgoal ;
	    let _ = Printf.printf " !! %a FAILURE\n%!" Pattneut.print chased in
	    mzero)]
    else
      x
  in

  let debugTraceEnter goalidx goal = 
    if !_DEBUG_DEMAND || isTraced_mutable goalidx then
      (let highlighted = highlightMetas goal in
       let chased = chasePattneut_mutable ~deep:true [] highlighted in
       let chased' = chasePattneut_mutable ~deep:true [] goal in
       let trace = Printf.sprintf "Enter %a\n%!" Pattneut.print chased in
       (* let trace = Printf.sprintf "Enter %a\n%!" (CheapPrint.neutdepth 2) chased in *)
       chased', true, trace)
    else
      goal, false, ""
  in
  let debugTraceExit indebug goal f =
    if indebug then
      (perform
	res <-- ifte f (fun x -> return (Some x)) (lazy(return None)) ;
        let highlighted = highlightMetas goal in
	chased <-- chasePattneut ~deep:true [] highlighted ;
        match res with
	    Some x -> Printf.printf "Exit %a\n%!" Pattneut.print chased ; return x
	  | None -> Printf.printf "Failed %a\n%!" Pattneut.print chased ; mzero)
	  (*   Some x -> Printf.printf "Exit %a\n%!" (CheapPrint.neutdepth 3) chased ; return x *)
	  (* | None -> Printf.printf "Failed %a\n%!" (CheapPrint.neutdepth 3) chased ; mzero) *)
    else 
      f
  in


  let eachConstructor initstate constructor = lazy(
    let indebug = ref false in
    let trace = ref "" in
    perform
      (result, ccond, cpremise, cg') <-- inmonad ~statewrite:true (fun _ -> try 

        tempstate := initstate ;

	(try
	   let _, cgoal, _, _ = getInfoFromClause (constructor.patt) in
	   fastFailUnify_mutable newgoal cgoal ~chase1:true ~chase2:constructor.prophasrunmetas
	 with MalformedClause(_) | UnknownPredicate(_) -> ()) ;

	let c', nu = allocateMetas_mutable constructor in

	let cgoalidx, cgoal, ccond, cpremise, c' = getInfoFromUnchasedClause_mutable c' in
	
	let cg', indebug', trace' = debugTraceEnter cgoalidx cgoal in

	trace := trace' ;
	indebug := indebug' ;

	pattUnifyFull_mutable newgoal cgoal ;
	ignore(List.map (uncurry nameUnify_mutable) nu) ;
	
	true, ccond, Some cpremise, Some cg'

	with PattUnifyError _ -> false, None, None, None) ;

      moneOrMzero result ;
      (match ccond with Some ccond -> demand ccond | None -> return ()) ;
      \ Printf.printf "%s" !trace ;

      debugTraceExit !indebug (Option.get cg')
	(demand (Option.get cpremise)))

  in

  perform
    let pred     =   headPredicate newgoal in
    _            <-- debugEnter pred ;
    constructors <-- findConstructors pred ;
    initstate    <-- getbacktrackstate ;
    _            <-- constructors |> List.map (eachConstructor initstate)
                     |> debugFailAppend initstate pred
		     |> msum ;

    opengoals    <-- getOpenGoals () ;
    _            <-- mapM (fun (p, env) -> perform
                            \ if !_DEBUG_DEMAND then Printf.printf "Deferred goal:\n" ;
                            inenv env (demand p)) opengoals ;

    return ()

and ensureStateRestored p =
  
  (* some builtin command doesn't backtrack properly --
     couldn't find it so this is a temporary remedy *)
  let open RunCtx.Monad in
  perform 
    state <-- getbacktrackstate ;
    ifte p return (lazy(perform
			  setstate state ;
			  mzero))

and _demand (premise : pattneut) : unit RunCtx.Monad.m =

  let open RunCtx.Monad in
  perform
    premise <-- chasePattneut [] premise ;
    let _ = headPredicate premise in
    let hd, args = match premise.term with `AppMany(hd, args, _) -> hd, args | _ -> assert false in
    let idx = match hd.term with `Var(_, (`Free, idx)) -> idx | _ -> assert false in
    match IMap.Exceptionless.find idx !builtin_predicates with

      Some builtin_code -> ensureStateRestored(builtin_code hd.classifier args)
    | None              -> demandNormal premise

and demand p =

  _demand p

and demandNormal p =
  logM (lazy(Printf.sprintf "demand %a" CheapPrint.neut p))
       (_demandNormal p)
;;


let defineClause (e : exprU) : unit RunCtx.Monad.m =
  let open RunCtx.Monad in
  perform 
      (idx, clause) <-- intermlang (fun _ -> checkClause e) ;
      state         <-- getstate ;
      _             <-- setstate { state with rsconstr_for_pred = IMap.modify_def [] idx (fun l -> l++[clause]) state.rsconstr_for_pred } ;
      return ()
;;


(* ------------------------------- *)
(* Some basic built-in predicates. *)
(* ------------------------------- *)

let new_builtin_predicate name typ code =
  let index = new_builtin name typ in
  builtin_predicates := IMap.add index code !builtin_predicates ;
  index
;;

module BuiltinProps = struct

  open RunCtx.Monad ;;


  (* success *)
  let _eiSuccess = new_builtin_predicate "success" (_tProp)
    (fun _ -> function [ ] -> begin perform
	
	return ()

    end | _ -> assert false)
  ;;

  (* failure *)
  let _eiFailure = new_builtin_predicate "failure" (_tProp)
    (fun _ -> function [ ] -> begin perform
	
	mzero

    end | _ -> assert false)
  ;;

  (* p1, p2 *)
  let _eiAnd = new_builtin_predicate "and" (_tProp **> _tProp **> _tProp)
    (fun _ -> function [ { term = `LamMany([], p1) } ;
			 { term = `LamMany([], p2) } ] -> begin perform
	
	_ <-- demand p1 ;
        _ <-- demand p2 ;
	return ()

    end | _ -> assert false)
  ;;

  (* p1; p2 *)
  let _eiOr = new_builtin_predicate "or" (_tProp **> _tProp **> _tProp)
    (fun _ -> function [ { term = `LamMany([], p1) } ;
			 { term = `LamMany([], p2) } ] -> begin perform
	
	state <-- getbacktrackstate ;
        (demand p1) // (lazy(perform
			  _ <-- setstate state;
			  demand p2))

    end | _ -> assert false)
  ;;

  (* (x:t -> p) *)
  let _eiNewvar = new_builtin_predicate "newvar" (( ~* "A" **> _tProp) **> _tProp)
    (fun _ -> function [ p ] -> begin perform
	
	p     <-- pattcanonRenormalize p ;
	p'    <-- chasePattcanon [] p ;
        (match p'.term with
	  `LamMany( [ { term = name, typ } ], p'') ->
	    perform
	      env  <-- getenv; 
	      env' <-- allocateFvar name typ;
	      _    <-- intermlang (fun _ -> kindcheck_type typ) ;
	      let p'' = freshenPatt (List.length env.renvars) p'' in
	      inenv env' (demand p'')
	| _ -> assert false)

    end | _ -> assert false)
  ;;

  (* [x:A]P *)
  let _eiNewmeta = new_builtin_predicate "newmeta" (( ~* "A" **> _tProp) **> _tProp)
    (fun _ -> function [ p ] -> begin perform
	
	p     <-- pattcanonRenormalize p ;
	p'    <-- chasePattcanon [] p ;
        (match p'.term with
	  `LamMany( [ { term = name, typ } ], p'') ->
	    perform
	      newvar <-- addRunMeta None ;
	      state  <-- getstate ;
	      let meta = { term = `Meta("_"^(string_of_int newvar), newvar, `Subst([], Some (IMap.empty, IMap.empty), [], []), typ ) ; classifier = typ ; loc = p'.loc ; extra = PattExtras.empty () } in
	      let subst' = [ { term = `LamMany( [], meta ); classifier = typ ; loc = p'.loc ; extra = PattExtras.empty () } ] in
	      let p'' = pattneutSubstMany subst' p'' in
	      demand p''
		
	| _ -> assert false)

    end | _ -> assert false)
  ;;

  (* [x:A]P *)
  let _eiNewFmeta = new_builtin_predicate "newfmeta" (( ~* "A" **> _tProp) **> _tProp)
    (fun _ -> function [ p ] -> begin perform

	p  <-- pattcanonRenormalize p ;
	p' <-- chasePattcanon [] p ;
        (match p'.term with
	  `LamMany( [ { term = name, typ } ], p'') ->
	    perform
	      newvar <-- addRunMeta ~mode:`Free None ;
	      state  <-- getstate ;
	      let meta = { term = `Meta("_"^(string_of_int newvar), newvar, `Subst([], Some (IMap.empty, IMap.empty), [], []), typ) ; classifier = typ ; loc = p'.loc ; extra = PattExtras.empty () } in
	      let subst' = [ { term = `LamMany( [], meta ); classifier = typ ; loc = p'.loc ; extra = PattExtras.empty () } ] in
	      let p'' = pattneutSubstMany subst' p'' in
	      demand p''

	| _ -> assert false)

    end | _ -> assert false)
  ;;

  (* [x:A]P *)
  let _eiNewNmeta = new_builtin_predicate "newnmeta" (( ~* "A" **> _tProp) **> _tProp)
    (fun _ -> function [ p ] -> begin perform
	
	p     <-- pattcanonRenormalize p ;
	p'    <-- chasePattcanon [] p ;
        (match p'.term with
	  `LamMany( [ { term = name, typ } ], p'') ->
	    perform
	      newvar <-- addRunMeta ~mode:`New None ;
	      state  <-- getstate ;
	      let meta = { term = `Meta("_"^(string_of_int newvar), newvar, `Subst([], Some (IMap.empty, IMap.empty), [], []), typ) ; classifier = typ ; loc = p'.loc ; extra = PattExtras.empty () } in
	      let subst' = [ { term = `LamMany( [], meta ); classifier = typ ; loc = p'.loc ; extra = PattExtras.empty () } ] in
	      let p'' = pattneutSubstMany subst' p'' in
	      demand p''

	| _ -> assert false)

    end | _ -> assert false)
  ;;

  (* (c -> p) *)
  let _eiAssume = new_builtin_predicate "assume"  (_tClause **> _tProp **> _tProp)
    (fun _ -> function [ c; { term = `LamMany([], p) } ] -> begin perform
	
         (* the check below would not work, even though it's disabled elsewhere anyway *)
         (* _           <-- intermlang (checkWellformedClause p1) ; *)
	 c              <-- chasePattcanon [] c ;
         let c = match c.term with `LamMany([], body) -> body | _ -> assert false in
         (idx, gl, a,b,c')  <-- inmonad ~statewrite:true (fun _ -> getInfoFromUnchasedClause_mutable c) ;
         _                  <-- intermlang (fun _ -> checkClauseNotBuiltin c' idx) ;
	 env'               <-- addTempConstructor idx c' ;
	 inenv env' (demand p)

    end | _ -> assert false)
  ;;
  

  let _eiIFTE = new_builtin_predicate "ifte" (_tProp **> _tProp **> _tProp **> _tProp)
    (fun _ -> function [ { term = `LamMany([], p1) } ;
			 { term = `LamMany([], p2) } ;
			 { term = `LamMany([], p3) } ] -> begin perform

	  state    <-- getbacktrackstate ;
          ifte (demand p1)
	       (fun _ -> demand p2)
	       (lazy(perform
		  _ <-- setstate state;
	  	  demand p3))

    end | _ -> assert false)
  ;;

  let _eiOnce = new_builtin_predicate "once" (_tProp **> _tProp)
    (fun _ -> function [ { term = `LamMany([], p) } ] -> begin perform

	once(demand p)

    end | _ -> assert false)
  ;;

  let _eiGuard = new_builtin_predicate "guard" ( ~* "A" **> _tProp **> _tProp )
    (fun _ -> function [ g ; { term = `LamMany([], p) } ] -> begin perform
	
	g <-- chasePattcanon [] g ;
        match g.term with

	  `LamMany(_, { term = `Meta(_,idx,_,_) }) ->
	    perform
	      env <-- getenv ;
	      addConstraint idx (`Demand(idx,None,p,env))

	| _ -> demand p

    end | _ -> assert false)
  ;;

  let _eiRemovableGuard = new_builtin_predicate "removableguard" ( _tUnit **> ~* "A" **> _tProp **> _tProp )
    (fun _ -> function [ r ; g ; { term = `LamMany([], p) } ] -> begin perform
	
	g <-- chasePattcanon [] g ;
        r <-- chasePattcanon [] r ;

        match r.term, g.term with
	    
	  `LamMany(_, { term = `Meta(_,removeidx,_,_) }),
	  `LamMany(_, { term = `Meta(_,guardidx,_,_) }) ->
	    perform
	      env <-- getenv ;
	      addConstraint guardidx (`Demand(guardidx,Some removeidx,p,env)) ;
	      addConstraint removeidx (`RemoveDemand(guardidx,removeidx))

	| `LamMany(_, { term = `Meta(_,removeidx,_,_) }), _ -> demand p

	| _ -> return ()

    end | _ -> assert false)
  ;;

  let _eiAssumeReset = new_builtin_predicate "assume_reset" ( ~* "A" **> _tProp **> _tProp )
    (fun _ -> function [ pred ; { term = `LamMany([], p) } ] -> begin perform

	pred <-- chasePattcanon [] pred ;
      
        match pred.term with
	    `LamMany(_, body) -> 
	      perform
  	        let idx = headPredicate body in
	        env' <-- resetTempConstructors idx ;
  	        inenv env' (demand p)

    end | _ -> assert false)
  ;;
        
 
end;;



(* main code ends. support code for top-level commands follows *)

let getMetaBoundNames (i : int) : name list RunCtx.Monad.m =
  let open RunCtx.Monad in
  perform
    state  <-- getstate ;
    let names = try IMap.find i state.rsmeta_boundnames with _ -> [] in
    names' <-- mapM chaseName names ;
    return names'
;;

let getMeta s t (i : int) : pattcanon RunCtx.Monad.m =
  let interm = intermlang in
  let open RunCtx.Monad in
  perform
     p <-- getMetaParent i ;
     match p with
	 Some (p, _) -> perform
	   _ <-- chasePattneut ~deep:true [] p ;
	   p <-- chasePattneut ~deep:true [] p ;
           boundnames <-- getMetaBoundNames i ;
	   res <-- inmonad (fun _ -> interm (fun _ -> reconstructLambdas t boundnames p)) ;
	   return res
       | None   -> 
         (let meta = { term = `Meta(s,i,`Subst([],None,[],[]),t) ; classifier = t ; loc = None ; extra = PattExtras.empty () } in
	  let canon = { term = `LamMany([], meta) ; classifier = t ; loc = None ; extra = PattExtras.empty () } in
	  chasePattcanon ~deep:true [] canon)
;;

let getOpenConstraints () : pattcanon list RunCtx.Monad.m =

  let open RunCtx.Monad in
 
  let fixConstraint (c : constraintT) : pattcanon option RunCtx.Monad.m = 
    match c with
      `Demand(_,_,c,_) -> perform
	                 c <-- pattneutRenormalize c ;
	                 c' <-- chasePattcanon [] c ;
			 return (Some c')
    | `Unif(_,n1,n2) -> return (Some
                        { n1 with term = `LamMany([], 
                        { n1 with term = `AppMany( { n1 with term = `Var(`Concrete("eq"), (`Free, 0)) },
						   [ pattneutToCanon n1 ; pattneutToCanon n2 ],
						   [ { n1 with term = () } ; { n2 with term = () } ]) }) })
    | `UnifCanon(_,n1,n2) -> return (Some
                             { n1 with term = `LamMany([],
                             { n1 with term = `AppMany( { n1 with term = `Var(`Concrete("eq"), (`Free, 0)) },
						   [ n1 ; n2 ],
						   [ { n1 with term = () } ; { n2 with term = () } ]) })})
    | `RemoveDemand(_,_) -> return None
  in

  perform
    
    is <-- inmonad ~statewrite:false (fun _ -> (!tempstate).rsmetaswithconstraints) ;
    c  <-- inmonad ~statewrite:false (fun _ -> List.map getConstraints_mutable (ISet.elements is)) ;
    cs <-- mapM fixConstraint (List.flatten c) ;
    return (List.filter_map id cs)
    

;;
    

let queryGoal ?(print = false) (goal : exprU) : (string * pattcanon) list RunCtx.Monad.m =

  let care_about n = 
    not (isNameMeta n || String.starts_with n "_")
  in
  
  (* TODO: meta handling is weird here, figure out proper way to do it *)
  let open RunCtx.Monad in
  perform 
    goal'     <-- intermlang (fun _ -> checkQuery goal) ;
    newmetas  <-- intermlang (fun _ ->
                                let state = !termstate in
			        let newmetas =
				  increasing state.metas |>
				      List.map (fun i -> i,
					IMap.find i state.meta_to_name,
					IMap.find i state.typ_of_meta)
				in
				let newmetas =
				  List.filter_map (fun (i, n, t) -> let t = chaseTypeDeep ~replaceUninst:true t () in
								    if care_about n then Some (i,n,t) else None)
				    newmetas
				in
				clearMetasInState () ;
				newmetas) ;
    state <-- getstate ;
    (goal'', nu) <-- inmonad ~statewrite:true (fun _ -> allocateMetas_mutable goal') ;
    let newmetas =
      List.map
	(fun (i, n, t) -> (i, n, shiftMetasTyp state.rstermstate.tmetas t))
	newmetas
    in
    _ <-- mapM (uncurry nameUnify) nu ;
    let _ = if print then Printf.printf "\n%a\n" Pattneut.alphaSanitizedPrint goal'' in

    _     <-- (demand goal'') //
              (lazy(perform
		       let _ = if print then Printf.printf "Impossible.\n" in
		       mzero)) ;

    state <-- getstate ;
    metas <-- mapM (fun (i, s, t) -> perform
                                        p <-- getMeta s t i ;
                                        return (s, p)) newmetas ;

    constraints <-- if print then getOpenConstraints () else return [] ;

    let dotOrColon = if List.is_empty metas then "." else ":" in
    let _ = if print then

      let names, metas = List.split metas in
      let metas' = Pattcanon.alphaSanitizedPrintMany metas in
      let combined = List.combine names metas' in

      let constraints' = Pattcanon.alphaSanitizedPrintMany constraints in
      let constraintsOrNot =
	if List.is_empty constraints || not(!_DEBUG_CONSTRAINTS) then ""
	else
	  Printf.sprintf "\nDeferred Constraints:\n%a"
	    (List.print ~first:"" ~last:"\n"
	       ~sep:"\n" String.print) constraints'
      in

      Printf.printf "Yes%s\n%a%s"
      dotOrColon

      (List.print ~first:"" ~last:"\n" ~sep:",\n"
	 (Pair.print ~first:"" ~last:"" ~sep:" := "
	    String.print String.print)) combined

      constraintsOrNot
    in
    return metas

;;




let observe (type a) (type b) (sk : a -> b RunCtx.BaseMonad.m)
                              (fk : (b RunCtx.BaseMonad.m) Lazy.t)
                              (e : a RunCtx.Monad.m) : b RunCtx.BaseMonad.m =
  e.twocont
    (fun result fk -> sk result)
    fk
;;


let impossibleGoal =
  (lazy(RunCtx.BaseMonad.return (Printf.printf "Impossible.\n")))
;;


exception PrologError;;
let prolog_handler e =
  try Lazy.force e
  with
  | UnknownPredicate(p) -> begin
    Printf.printf "In %s:\n  The predicate in %a is not concrete.\n"
      (UChannel.string_of_span p.loc)
      Pattneut.alphaSanitizedPrint p;
    raise PrologError
    end
  | MalformedClause(p) -> begin
    Printf.printf "In %s:\n  The clause %a is malformed.\n"
      (UChannel.string_of_span p.loc)
      Pattneut.alphaSanitizedPrint p;
    raise PrologError
  end
  | MalformedClauseTypecase(p,t,t') -> begin
    Printf.printf "In %s:\n  The clause conclusion %a specializes parametric type variables.\n  Expected type: %a\n  Actual type: %a\n"
      (UChannel.string_of_span p.loc)
      Pattneut.alphaSanitizedPrint p
      Typ.print t Typ.print t';
    raise PrologError
  end
  | ClauseForBuiltin(p,s) -> begin
    Printf.printf "In %s:\n  Cannot add new clause to builtin predicate %s.\n"
      (UChannel.string_of_span p.loc)
      s;
    raise PrologError
  end
;;

(* ------------------------------
   Global state manipulation.
   -----------------------------
 *)
let globalprolog_do ?(failure = lazy(raise PrologError)) e =
  
  let state = { !globalprologstate with rstermstate = !globalstate } in
  let ctx = { env = empty_run_env () ; state = state } in
  let (res, state') = prolog_handler (lazy(observe RunCtx.BaseMonad.return failure e ctx)) in
  let state' = clearRunMetas state' in
  globalprologstate := state' ;
  globalstate := state'.rstermstate ;
  res

;;


let global_new_clause clause =
  let open RunCtx.Monad in
  globalprolog_do (perform
		     clause <-- intermlang clause ;
		     defineClause clause)
;;

let global_query goal =
  let open RunCtx.Monad in
  globalprolog_do (* ~failure:impossibleGoal *)
    (perform
       goal <-- intermlang goal ;
       (perform
	   _ <-- queryGoal ~print:true goal ;
           return ()) // (lazy(return ())))
;;

let global_trace b goal =
  let open RunCtx.Monad in
  globalprolog_do (perform
		     goal <-- intermlang goal ;
		     goal <-- intermlang (fun _ -> typeof goal) ;
		     idx  <-- (match goal.term with `Var(_, (`Free, idx)) -> return idx | _ -> mzero) ;
		     setTracedIndex b idx)
;;

exception ResetInModule of string ;;
let global_reset () =
  match (!globalstate).current_module with
  | Some m -> raise (ResetInModule m)
  | _ -> (global_term_reset () ;
	  globalprologstate := !builtinprologstate)
;;


let meta_do = ref (fun (s : string) -> ()) ;;

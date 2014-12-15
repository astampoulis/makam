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
open Termlangcanon;;
open Termlangbuiltin;;
open Termlangprolog;;
open Termlangext;;
open Utils;;


new_builtin_predicate "lookup" ( _tString **> ( ~* "A" ) **> _tProp )
  (let open RunCtx.Monad in
   fun _ -> fun [ varname ; res ] -> perform
       varname <-- chasePattcanon [] varname ;
       varname <-- _PtoString varname ;
       let expr = pattcanonToExpr (-1) res in
       varidx  <-- intermlang (fun _ ->
	 try Some (findUnifiableVar `Free (findFvar varname) (exprAsExprU expr))
	 with _ -> None) ;
       match varidx with
       | Some (`Free, varidx) ->
	 let patt = pattheadToCanon { expr with term = `Var(`Concrete(varname), (`Free, varidx)) } in
	 pattcanonUnifyFull res patt
       | _ -> mzero)
;;

new_builtin_predicate "headname" ( ( ~* "A" ) **> _tString **> _tProp )
  (let open RunCtx.Monad in
   fun _ -> fun [ patt ; res ] -> perform
       patt <-- pattcanonRenormalize patt ;
       patt <-- chasePattcanon [] patt ;
       match patt.term with
	 | `LamMany(_, { term = `AppMany( { term = `Var(`Concrete(s), (`Free, _)) }, _, _ ) }) ->
	   pattcanonUnifyFull res (_PofString ~loc:patt.loc s)
	 | _ -> mzero)
;;

new_builtin_predicate "headargs" ( ( ~* "A" ) **> ( ~* "B" ) **> (_tList _tDyn) **> _tProp)
  (let open RunCtx.Monad in
   fun _ -> fun [ term ; head ; args ] -> perform
     term <-- pattcanonRenormalize term ;
     term <-- chasePattcanon [] term ;
     match term.term with

       (* deconstruct *)
       | `LamMany([], { term = `AppMany(hd, args', args'info) }) ->

	 perform
	   hd <-- pattcanonRenormalize (pattheadToCanon hd) ;
	   pattcanonUnifyFull head hd ;
	   let args' = List.map (fun e -> _PofDyn ~loc:e.loc e) args' in
	   let args'list = _PofList ~loc:term.loc _tDyn args' in
	   pattcanonUnifyFull args args'list

       (* reconstruct *)
       | `LamMany([], { term = `Meta(_) }) ->
	 perform
	   args <-- _PtoList args ;
	   ps <-- mapM pattcanonRenormalize (head :: args) ;
	   ps <-- mapM (chasePattcanon []) ps ;
	   let (head' :: args') = ps in
	   (head'', argsinfo, typ) <--
	     (match head'.term with
		 `LamMany(_, { term = `AppMany(hd, _, argsinfo) ;
			       classifier = typ }) ->
		   return (hd, argsinfo, typ)
	       | _ -> mzero) ;

	   (* check types *)
	   argstyps <-- intermlang (fun _ -> gatherArrowTyps head''.classifier) ;
	   if (List.length args' <> List.length argstyps) then mzero else return () ;
	   args' <-- mapM (uncurry _PtoDyn) (List.combine args' argstyps) ;

	   let term' =
	     pattneutToCanon
	       { term = `AppMany(head'', args', argsinfo) ;
		 classifier = typ ;
		 loc = head.loc ;
		 extra = PattExtras.empty () }
	   in
	   pattcanonUnifyFull term term'

       | _ -> mzero)
;;

new_builtin_predicate "decomposeunif" ( ( ~* "A" ) **> _tInt **> (_tList _tDyn) **> _tProp)
  (let open RunCtx.Monad in
   fun _ -> fun [ term ; index ; args ] -> perform
     term <-- pattcanonRenormalize term ;
     term <-- chasePattcanon [] term ;
     match term.term with

       (* deconstruct *)
       | `LamMany([], { term = `Meta(_, idx, `Subst(args', _, args'info, _), _) }) ->

	 perform
	   pattcanonUnifyFull index (pattcanonInt idx) ;
	   let args' = List.map (fun e -> _PofDyn ~loc:e.loc e) args' in
	   let args'list = _PofList ~loc:term.loc _tDyn args' in
	   pattcanonUnifyFull args args'list

       | _ -> mzero)
;;

new_builtin_predicate "recomposeunif" ( ( ~* "A" ) **> (_tList _tDyn) **> ( ~* "A" ) **> _tProp)
  (let open RunCtx.Monad in
   fun _ -> fun [ term ; args ; result ] -> perform
     term <-- pattcanonRenormalize term ;
     term <-- chasePattcanon [] term ;
     match term.term with

       (* reconstruct *)
       | `LamMany([], ({ term = `Meta(s, idx, `Subst(_, _, argsinfo, names), typ) } as neut)) ->
	 perform
	   args <-- _PtoList args ;
	   ps <-- mapM pattcanonRenormalize args ;
	   ps <-- mapM (chasePattcanon []) ps ;

	   (* check types *)
	   argstyps <-- intermlang (fun _ -> gatherArrowTyps typ) ;
	   if (List.length ps <> List.length argstyps) then mzero else return () ;
	   args' <-- mapM (uncurry _PtoDyn) (List.combine ps argstyps) ;

	   let term' =
	     pattneutToCanon
	       { neut with
		 term = `Meta(s, idx, `Subst(args', None, argsinfo, names), typ) }
	   in
	   pattcanonUnifyFull term' result

       | _ -> mzero)
;;

new_builtin_predicate "isunif" ( ~* "A" **> _tProp )
  (fun _ -> fun [ p ] ->
    (let open RunCtx.Monad in
     perform
       state  <-- getstate ;
       p      <-- chasePattcanon ~deep:true [] p ;
       _      <-- setstate state ;
       let isunif = match p.term with `LamMany(_, { term = `Meta _ }) -> true | _ -> false in
       moneOrMzero isunif))
;;



(* types and terms for staged commands and so on *)
let _tiCmd, _tCmd   = new_builtin_type "cmd" ;;
let _eiCmdNewClause = new_builtin "cmd_newclause" (_tClause **> _tCmd) ;;
let _eiCmdNewTerm   = new_builtin "cmd_newterm"   (_tString **> ( ~* "A" ) **> _tCmd) ;;
let _eiCmdMany      = new_builtin "cmd_many"      (_tList _tCmd **> _tCmd) ;;
let _eiCmdStage     = new_builtin "cmd_stage"     ( (_tCmd **> _tProp) **> _tCmd ) ;;
let _eiCmdNone      = new_builtin "cmd_none"      _tCmd ;;
let _eiCmdQuery     = new_builtin "cmd_query"     ( _tProp **> _tCmd ) ;;


let exprRemoveUnresolved (e : expr) : exprU =

  let rec eaux e =
    let e = { e with classifier = taux e.classifier } in
    match e.term with
    | `Var(`Concrete(s), (`Meta, i)) ->
	let s = if s = "" then "X" else s in
	{ e with term = `Var(`Concrete(s ^ "~" ^ (string_of_int i)), None) }
    | `Var(_, (`Meta, i)) -> assert false
    | `App(e1,e2)  -> { e with term = `App(eaux e1, eaux e2) }
    | `Lam(s,t,e') -> { e with term = `Lam(s, taux t, eaux e') }
    | `Var(s,idx)  -> { e with term = `Var(s, Some idx) }
    | `Const(o)    -> { e with term = `Const(o) }
  and taux t =
    match t.term with
      `TVar(s, Some (`Meta, i), args) ->
	let s = if s = "" then "X" else s in
	{ t with term = `TVar(s ^ "~" ^ (string_of_int i), None, args) }
    | `TVar(s, idx, args) -> { t with term = `TVar(s, idx, List.map taux args) }
    | `Arrow(t1, t2) -> { t with term = `Arrow(taux t1, taux t2) }
    | `TypeSort -> t
    | `Forall(_,_) -> assert false
  in

  eaux e

;;


let getQueryResult (t : typ) (code : exprU) : exprU RunCtx.Monad.m =

  let open RunCtx.Monad in
  perform
    code   <-- intermlang (let code' = mkAnnot ~loc:code.loc (fun _ -> code) (t **> _tProp) in
			   mkApp ~loc:code.loc code' (mkVar "Result~~")) ;
    metas  <-- ifte (queryGoal ~print:false code) (fun x -> return (Some x))
      (lazy(Printf.printf "Error in staged code at %s.\n" (UChannel.string_of_span code.loc); return None)) ;
    result <-- (match metas with Some metas -> intermlang (fun _ ->
      let result = List.assoc "Result~~" metas in
      let result = 
	try
	  result |> pattcanonToExpr (-1) |> chaseTypesInExpr ~replaceUninst:true ~metasAreFine:true |>
	            alphaSanitize |> exprRemoveUnresolved
	with NewVarUsed -> assert false
      in
      Some result) | None -> return None);
    state  <-- getstate ;
    setstate (clearRunMetas state) ;
    (match result with Some result -> return result | None -> mzero)
      
;;

let _EUtoList  (xs : exprU) : exprU list =
  let rec aux s acc = 
    match s.term with
      `Var(_, Some (`Free, idx)) when idx = _eiNil -> List.rev acc
    | `App({ term = `App({ term =
	`Var(_, Some (`Free, idx)) }, hd)}, tl)
        when idx = _eiCons ->
      aux tl (hd :: acc)
    | _ -> assert false
  in
  aux xs []
;;


let _DEBUG_STAGING = ref false ;;

let rec doCommand (e : exprU) : unit RunCtx.Monad.m =
  
  let open RunCtx.Monad in
  let hd, args = ExprU.gatherApp e in
  let postCleanupMetas e =
    perform
      _     <-- e ;
      state <-- getstate ;
      setstate (clearRunMetas state)
  in
  postCleanupMetas begin
  match hd.term, args with

  | `Var(_, Some (`Free, idx)), [ clause ] when idx = _eiCmdNewClause ->

    let _ = if !_DEBUG_STAGING then Printf.printf "new clause %a\n" (ExprU.print ~debug:true) clause in
    defineClause clause
      
  | `Var(_, Some (`Free, idx)), [ { term = `Const(o) } ; typterm ] when idx = _eiCmdNewTerm ->

    let _ = if !_DEBUG_STAGING then Printf.printf "new term %s : %a\n" (Obj.obj o) Typ.print typterm.classifier in
    intermlang (fun _ -> typedecl (Obj.obj o) typterm.classifier () |> ignore)

  | `Var(_, Some (`Free, idx)), [ list ] when idx = _eiCmdMany ->

    perform
      _ <-- mapM doCommand (_EUtoList list) ;
      return ()

  | `Var(_, Some (`Free, idx)), [ code ] when idx = _eiCmdStage ->

    perform
      cmd <-- getQueryResult _tCmd code ;
      doCommand cmd

  | `Var(_, Some (`Free, idx)), [] when idx = _eiCmdNone ->
    
    return ()

  | `Var(_, Some (`Free, idx)), [ query ] when idx = _eiCmdQuery ->
    
    (perform
	   _ <-- queryGoal ~print:true query ;
           return ()) // (lazy(return ()))

  | _ -> mzero
  end

;;


let doStagedCommand (code : exprU) : unit RunCtx.Monad.m =
  
  let open RunCtx.Monad in
  perform
    cmd <-- getQueryResult _tCmd code ;
    ifte (doCommand cmd) return
      (lazy(Printf.printf "Error in staged code at %s.\n"
	      (UChannel.string_of_span code.loc); mzero))

;;
    

let global_staged_command cmdcode =
  
  let open RunCtx.Monad in
  globalprolog_do (perform
                    cmdcode <-- intermlang cmdcode ;
		    doStagedCommand cmdcode)

;;

(* global_command_do --
     if no extensions are enabled, just docommand cmd
     if any is enabled, then create the proper query and
     then do it.. (mkLam (fold2 (.. mkApp (mkApp (mkIVar eiAnd) cur) (mkapp elm1 elm2))
                          l1 = [ map mkIVar extensionsIndexes ]
                          l2 = [ (cmd), "X1", "X2" ... ]
                          l3 = [ "X1", "X2", ... , mkIVar (`Bound 0) ]))
*)


exception CompilationFailure ;;

new_builtin_predicate "unsafe.eval_ocaml" ( _tString **> _tProp )
  (let open RunCtx.Monad in
   fun _ -> fun [ ocamlcode ] -> perform
       ocamlcode <-- chasePattcanon [] ocamlcode ;
       ocamlstring <-- _PtoString ocamlcode ;
       (try !(Termlangprolog.meta_do) ocamlstring;
            return ()
        with CompilationFailure -> begin
            Printf.printf "In %s:\n  Compilation error.\n"
                          (UChannel.string_of_span ocamlcode.loc);
            mzero
          end))
;;

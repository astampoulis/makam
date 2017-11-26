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


builtin_enter_module "refl" ;;

  new_builtin_predicate "lookup" ( _tString **> ( ~* "A" ) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ varname ; res ] -> begin perform
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
         | _ -> mzero
    end | _ -> assert false)
  ;;

  new_builtin_predicate "open_constraints" ( ~* "A" **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ term ] -> begin perform
       term <-- pattcanonRenormalize term ;
       term <-- chasePattcanon [] term ;
       match term.term with

         (* deconstruct *)
         | `LamMany([], { term = `Meta(_, idx, _, _) }) ->
            perform
              state  <-- getstate ;
              moneOrMzero (Termlangcanon.ISet.mem idx state.rsmetaswithconstraints)

         | _ -> mzero

    end | _ -> assert false)
  ;;

  new_builtin_predicate "headname" ( ( ~* "A" ) **> _tString **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ patt ; res ] -> begin perform
         patt <-- pattcanonRenormalize patt ;
         patt <-- chasePattcanon [] patt ;
         match patt.term with
           | `LamMany(_, { term = `AppMany( { term = `Var(`Concrete(s), (`Free, _)) }, _, _ ) }) ->
             pattcanonUnifyFull res (_PofString ~loc:patt.loc s)
           | _ -> mzero
    end | _ -> assert false)
  ;;

  new_builtin_predicate "headargs" ( ( ~* "A" ) **> ( ~* "B" ) **> (_tList _tDyn) **> _tProp)
    (let open RunCtx.Monad in
     fun _ -> function [ term ; head ; args ] -> begin perform
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

         | _ -> mzero

    end | _ -> assert false)
  ;;

  let pattOfConstant name idx =
    let expru = mkIndexedVar ~name:(`Concrete(name)) (`Free, idx) () in
    let expr = typeof expru in
    let patt =
      match expr with
        ({ term = `Var(`Concrete(name), (`Free, idx)) } as e) ->
          { e with term = `Var(`Concrete(name), (`Free, idx)) }
          |> pattheadToCanon
      | _ -> assert false
    in
    patt
  ;;

  new_builtin_predicate "duphead" ( (~* "A") **> ( ~* "B" ) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ var ; res ] -> begin perform
         var <-- pattcanonRenormalize var;
         var <-- chasePattcanon [] var ;
         (name, idx) <-- begin
           match var.term with
             `LamMany(_, { term = `AppMany( { term = `Var(`Concrete(name), (`Free, idx)) }, _, _ ) }) ->
               return (name, idx)
           | _ -> mzero
           end;
         newvar <-- intermlang (fun _ -> pattOfConstant name idx);
         pattcanonUnifyFull res newvar
    end | _ -> mzero)
  ;;

  new_builtin_predicate "allconstants" ( (_tList _tDyn) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ res ] -> begin perform
         vars <-- intermlang (fun _ ->
           let idxs  = increasing !termstate.fvars in
           let names = List.map nameOfFVar idxs in
           let patts = List.map2 pattOfConstant names idxs in
           let dynpatts = List.map _PofDyn patts in
           let list = _PofList _tDyn dynpatts in
           list);
         pattcanonUnifyFull res vars
     end | _ -> assert false)
  ;;

  new_builtin_predicate "assume_get" ( ~* "A" **> (_tList _tClause) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; unif ] -> begin perform

        pred <-- pattcanonRenormalize pred ;
        pred <-- chasePattcanon [] pred ;

        match pred.term with
            `LamMany(_, body) ->
              perform
                let idx  =   headPredicate body in
                env      <-- getenv ;
                let cs   =   try Termlangcanon.IMap.find idx env.retemp_constr_for_pred with Not_found -> [] in
                cs'      <-- inmonad ~statewrite:true (fun _ -> List.map (pattneutToCanon % fst % allocateMetas_mutable) cs) ;
                pattcanonUnifyFull unif (_PofList ~loc:pred.loc _tClause cs')

    end | _ -> assert false)
  ;;

  new_builtin_predicate "assume_reset" ( ~* "A" **> _tProp **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; { term = `LamMany([], p) } ] -> begin perform

        pred <-- chasePattcanon [] pred ;

        match pred.term with
            `LamMany(_, body) ->
              perform
                let idx = headPredicate body in
                env' <-- resetTempConstructors idx ;
                inenv env' (demand p)

    end | _ -> assert false)
  ;;

  new_builtin_predicate "rules_get" ( ~* "A" **> (_tList _tClause) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; unif ] -> begin perform

        pred <-- pattcanonRenormalize pred ;
        pred <-- chasePattcanon [] pred ;

        match pred.term with
            `LamMany(_, body) ->
              perform
                  let idx  =   headPredicate body in
                  cs       <-- findConstructors idx ;
                  cs'      <-- inmonad ~statewrite:true (fun _ -> List.map (pattneutToCanon % fst % allocateMetas_mutable) cs) ;
                  pattcanonUnifyFull unif (_PofList ~loc:pred.loc _tClause cs')

    end | _ -> assert false)
  ;;

  new_builtin_predicate "rules_get_applicable" ( ~* "A" **> (_tList _tClause) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; unif ] -> begin perform

        pred <-- pattcanonRenormalize pred ;
        pred <-- chasePattcanon [] pred ;

        match pred.term with
            `LamMany(_, body) ->
              perform
                  let idx  =   headPredicate body in
                  cs       <-- findConstructors idx ;
                  state    <-- getbacktrackstate ;
                  csAppl   <-- mapM (fun c -> perform
                                                applies <-- constructorApplies state body c ;
                                                return (if applies then Some c else None)) cs;
                  let cs'  = List.filter_map identity csAppl in
                  cs''     <-- inmonad ~statewrite:true (fun _ -> List.map (pattneutToCanon % fst % allocateMetas_mutable) cs') ;
                  pattcanonUnifyFull unif (_PofList ~loc:pred.loc _tClause cs'')

    end | _ -> assert false)
  ;;

  new_builtin_predicate "isunif" ( ~* "A" **> _tProp )
    (fun _ -> function [ p ] -> begin
      (let open RunCtx.Monad in
       perform
         state  <-- getstate ;
         p      <-- pattcanonRenormalize p ;
         p      <-- chasePattcanon [] p ;
         _      <-- setstate state ;
         let isunif = match p.term with `LamMany([], { term = `Meta _ }) -> true | _ -> false in
         moneOrMzero isunif)
      end | _ -> assert false)
  ;;

  new_builtin_predicate "isconst" ( ~* "A" **> _tProp )
    (fun _ -> function [ p ] ->
      (let open RunCtx.Monad in
       perform
         state  <-- getstate ;
         p      <-- pattcanonRenormalize p ;
         p      <-- chasePattcanon [] p ;
         _      <-- setstate state ;
         let isconst = match p.term with
             `LamMany([], { term = `AppMany( { term = `Const _ }, [], [] ) }) -> true
           | _ -> false
         in
         moneOrMzero isconst)
     | _ -> assert false)
  ;;

  new_builtin_predicate "isbaseterm" ( ~* "A" **> _tProp )
    (fun _ -> function [ p ] ->
      (let open RunCtx.Monad in
       perform
         state  <-- getstate ;
         p      <-- pattcanonRenormalize p ;
         p      <-- chasePattcanon [] p ;
         _      <-- setstate state ;
         let isbaseterm = match p.term with
             `LamMany([], { term = `AppMany( { term = `Var (_, _) }, _, _ ) }) -> true
           | _ -> false
         in
         moneOrMzero isbaseterm)
     | _ -> assert false)
  ;;

  new_builtin_predicate "isfvar" ( ~* "A" **> _tProp )
    (fun _ -> function [ p ] ->
      (let open RunCtx.Monad in
       perform
         state  <-- getstate ;
         p      <-- pattcanonRenormalize p ;
         p      <-- chasePattcanon [] p ;
         _      <-- setstate state ;
         let isbaseterm = match p.term with
             `LamMany([], { term = `AppMany( { term = `Var (_, (`Free, _)) }, _, _ ) }) -> true
           | _ -> false
         in
         moneOrMzero isbaseterm)
     | _ -> assert false)
  ;;

  new_builtin_predicate "isnvar" ( ~* "A" **> _tProp )
    (fun _ -> function [ p ] ->
      (let open RunCtx.Monad in
       perform
         state  <-- getstate ;
         p      <-- pattcanonRenormalize p ;
         p      <-- chasePattcanon [] p ;
         _      <-- setstate state ;
         let isbaseterm = match p.term with
             `LamMany([], { term = `AppMany( { term = `Var (_, (`New, _)) }, _, _ ) }) -> true
           | _ -> false
         in
         moneOrMzero isbaseterm)
     | _ -> assert false)
  ;;

  new_builtin_predicate "isfun" ( ~* "A" **> _tProp )
    (fun _ -> function [ p ] ->
      (let open RunCtx.Monad in
       perform
         state  <-- getstate ;
         p      <-- pattcanonRenormalize p ;
         p      <-- chasePattcanon [] p ;
         _      <-- setstate state ;
         let isfun = match p.term with
             `LamMany(hd :: _, _) -> true
           | _ -> false
         in
         moneOrMzero isfun)
     | _ -> assert false)
  ;;

  (* --- more low-level operations with metavariables --- *)
  new_builtin_predicate "decomposeunif" ( ( ~* "A" ) **> _tInt **> (_tList _tDyn) **> _tProp)
    (let open RunCtx.Monad in
     fun _ -> function [ term ; index ; args ] -> begin perform
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

         | _ -> mzero
    end | _ -> assert false)
  ;;

  new_builtin_predicate "recomposeunif" ( ( ~* "A" ) **> (_tList _tDyn) **> ( ~* "A" ) **> _tProp)
    (let open RunCtx.Monad in
     fun _ -> function [ term ; args ; result ] -> begin perform
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

         | _ -> mzero
    end | _ -> assert false)
  ;;

  new_builtin_predicate "unifmetalevel" ( ( ~* "A" ) **> _tInt **> _tProp)
    (let open RunCtx.Monad in
     fun _ -> function [ term ; level ] -> begin perform
       term <-- pattcanonRenormalize term ;
       term <-- chasePattcanon [] term ;
       match term.term with

         (* deconstruct *)
         | `LamMany([], { term = `Meta(m1) }) ->

          perform
             lvl <-- getMetaLevel (metaindex m1);
             pattcanonUnifyFull level (pattcanonInt lvl) ;

         | _ -> mzero
    end | _ -> assert false)
  ;;

  let ensure_concrete_type (p : pattcanon) : unit RunCtx.Monad.m =
    let open RunCtx.Monad in
    perform
      t <-- intermlang (fun _ -> chaseType p.classifier) ;
      let b = match t.term with `TVar(_, Some (`Free, _), _) -> true | _ -> false in
      if b then return () else (Printf.printf "wrong call to external predicate expecting concrete type\n"; mzero)

  ;;

  exception TypStringUninstantiatedTMetas;;
  new_builtin_predicate "typstring" ( ( ~* "A" ) **> _tString **> _tProp)
  (fun _ -> fun [ e ; s ] ->
    (let open RunCtx.Monad in
     perform
     e <-- pattcanonRenormalize e ;
     p <-- chasePattcanon ~deep:true [] e ;
     state <-- getbacktrackstate;
     p' <-- intermlang (fun _ ->
              try
                let p' =
                 p |> pattcanonToExpr 0
                   |> chaseTypesInExpr ~replaceUninst:false ~metasAreFine:true
                in
                traverseTypeDeep
                        ~uninstantiatedMeta:(fun _ -> raise TypStringUninstantiatedTMetas)
                        p'.classifier;
                Some p'
               with TypStringUninstantiatedTMetas -> None);
     setstate state;
     match p' with
       Some p' ->
       (let res = Printf.ksprintf2 (fun s -> s) "%a" Typ.print p'.classifier in
        pattcanonUnifyFull s (_PofString ~loc:e.loc res))
     | None -> mzero))
  ;;

  new_builtin_predicate "getunif" ( ~* "A" **> ~* "B" **> _tProp )
    (fun _ -> function [ input ; output ] -> begin
      (let open RunCtx.Monad in
       let combine r1 r2 =
         match r1, r2 with
           Some r, None | None, Some r -> Some r
         | Some (l1, u1), Some (l2, u2) -> if l1 < l2 then Some (l1, u1) else Some (l2, u2)
         | None, None -> None
       in
       let rec auxneut cur (p : pattneut) =
         match p.term with
           `Meta(m1) ->
             perform
               ifte (perform
                       b <-- intermlang(fun _ -> typUnifyBool ~allow_instantiation:false p.classifier output.classifier) ;
                       moneOrMzero b)
                    (fun () -> perform
                       level <-- getMetaLevel (metaindex m1) ;
                       return (combine cur (Some (level, p))))
                    (lazy(foldM auxcanon cur (metasubstmain m1)))
         | `AppMany(hd, args, _) ->
             foldM auxcanon cur args
       and auxcanon cur (p : pattcanon) =
         match p.term with
           `LamMany(lamsinfo, p) -> auxneut cur p
       in
       perform
         _     <-- mapM ensure_concrete_type [ input ; output ] ;
         p     <-- chasePattcanon ~deep:true [] input ;
         p     <-- (match p.term with `LamMany([], p) -> return p | _ -> mzero) ;
         unif  <-- auxneut None p ;
         match unif, output.term with
           Some (_, unif), `LamMany([], { term = `Meta(o) }) ->
             (* pattUnifyFull output unif *)
             setMetaParent (metaindex o) unif
         | _           -> mzero)
     end | _ -> assert false)
  ;;

  new_builtin_predicate "absunif" ( ~* "A" **> ~* "B" **> (~* "B" **> ~* "A") **> _tProp )
    (fun _ [ term ; meta ; output ] ->
      (let open RunCtx.Monad in
       let getmetaindexcanon p = match p.term with `LamMany([], { term = `Meta(m) }) -> Some (metaindex m) | _ -> None in
       let getmetaindexneut p = match p.term with `Meta(m) -> Some (metaindex m) | _ -> None in
       let chaseWithConstraints uvar =
         let rec aux visited tovisit tovisit_set =
           match tovisit with
             [] -> return visited
           | uvar :: tl when ISet.mem uvar visited -> aux visited tl (ISet.remove uvar tovisit_set)
           | uvar :: tl ->
             (perform
                let visited = ISet.add uvar visited in
                let tovisit_set = ISet.remove uvar tovisit_set in
                cs  <-- getConstraints uvar ;
                cs' <-- mapM (fun elm ->
                              match elm with
                                `UnifCanon(bound, p1, p2) -> perform
                                                               state <-- getbacktrackstate ;
                                                               p1 <-- chasePattcanon bound p1 ;
                                                               p2 <-- chasePattcanon bound p2 ;
                                                               setstate state ;
                                                               return (List.filter_map getmetaindexcanon [ p1 ; p2 ])
                              | `Unif(bound, p1, p2) -> perform
                                                          state <-- getbacktrackstate ;
                                                          p1 <-- chasePattneut bound p1 ;
                                                          p2 <-- chasePattneut bound p2 ;
                                                          setstate state ;
                                                          return (List.filter_map getmetaindexneut [ p1 ; p2 ])
                              | _ -> return []) cs;
                let cs' = List.flatten cs' in
                let newones = List.filter (fun elm -> not (ISet.mem elm visited || ISet.mem elm tovisit_set)) cs' in
                aux visited (newones ++ tl) (ISet.union (newones |> List.enum |> ISet.of_enum) tovisit_set))
         in
         aux ISet.empty [uvar] (ISet.singleton uvar)
       in
       let rec auxneut bound uvars p : pattneut =
         match p.term with
           `Meta(m1) when ISet.mem (metaindex m1) uvars ->
             let head = { p with term = `Var(`Anon, (`Bound, bound)) } in
             let neut = { p with term = `AppMany(head, [], []) } in
             neut
         | `Meta(s,idx,`Subst(subst,substinv,ts,names),t) ->
           let subst = List.map (auxcanon bound uvars) subst in
           let substinv = invertSubst subst in
           { p with term = `Meta(s,idx,`Subst(subst,substinv,ts,names),t) }
         | `AppMany(hd, args, argsinfo) ->
           { p with term = `AppMany(hd, List.map (auxcanon bound uvars) args, argsinfo) }
         | _ -> assert false
       and auxcanon bound uvars p : pattcanon =
         match p.term with
           `LamMany(lamsinfo, body) -> { p with term = `LamMany(lamsinfo, auxneut (bound + List.length lamsinfo) uvars body) }
       in
       perform
         _    <-- mapM ensure_concrete_type [ term ; meta ] ;
         p    <-- chasePattcanon ~deep:true [] term ;
         meta <-- chasePattcanon ~deep:true [] meta ;
         uvar <-- (match getmetaindexcanon meta with Some i -> return i | _ -> mzero);
         uvars <-- chaseWithConstraints uvar ;
         p     <-- (match p.term with `LamMany([], p) -> return p | _ -> mzero) ;
         let ctx = auxneut 0 uvars p in
         let restyp = meta.classifier **> term.classifier in
         let res = { term = `LamMany( [ { term = (`Anon, meta.classifier) ; classifier = restyp ; loc = p.loc ; extra = PattExtras.empty () } ], ctx ) ;
                     classifier = restyp ;
                     loc = p.loc ; extra = PattExtras.empty () }
         in
         pattcanonUnifyFull output res))
  ;;

builtin_leave_module ();;



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

    ifte (queryGoal ~print:true query) (fun _ -> return ()) (lazy(return ()))

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

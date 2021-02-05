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
     fun _ -> function [ varname ; res ] -> begin
         let* varname = chasePattcanon [] varname in
         let* varname = _PtoString varname in
         let expr = pattcanonToExpr (-1) res in
         let* varidx = intermlang (fun _ ->
           try Some (findUnifiableVar `Free (findFvar varname) (exprAsExprU expr))
           with _ -> None) in
         match varidx with
         | Some (`Free, varidx) ->
           let patt = pattheadToCanon { expr with term = `Var(`Concrete(varname), (`Free, varidx)) } in
           pattcanonUnifyFull res patt
         | _ -> mzero
    end | _ -> assert false)
  ;;

  new_builtin_predicate "open_constraints" ( ~* "A" **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ term ] -> begin
       let* term = pattcanonRenormalize term in
       let* term = chasePattcanon [] term in
       match term.term with

         (* deconstruct *)
         | `LamMany([], { term = `Meta(_, idx, _, _) }) ->
              let* state = getstate in
              moneOrMzero (Termlangcanon.ISet.mem idx state.rsmetaswithconstraints)

         | _ -> mzero

    end | _ -> assert false)
  ;;

  new_builtin_predicate "headname" ( ( ~* "A" ) **> _tString **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ patt ; res ] -> begin
         let* patt = pattcanonRenormalize patt in
         let* patt = chasePattcanon [] patt in
         match patt.term with
           | `LamMany(_, { term = `AppMany( { term = `Var(`Concrete(s), (`Free, _)) }, _, _ ) }) ->
             pattcanonUnifyFull res (_PofString ~loc:patt.loc s)
           | _ -> mzero
    end | _ -> assert false)
  ;;

  new_builtin_predicate "headargs" ( ( ~* "A" ) **> ( ~* "B" ) **> (_tList _tDyn) **> _tProp)
    (let open RunCtx.Monad in
     fun _ -> function [ term ; head ; args ] -> begin
       let* term = pattcanonRenormalize term in
       let* term = chasePattcanon [] term in
       match term.term with

         (* deconstruct *)
         | `LamMany([], { term = `AppMany(hd, args', args'info) }) ->

             let* hd = pattcanonRenormalize (pattheadToCanon hd) in
             let* _ = pattcanonUnifyFull head hd in
             let args' = List.map (fun e -> _PofDyn ~loc:e.loc e) args' in
             let args'list = _PofList ~loc:term.loc _tDyn args' in
             pattcanonUnifyFull args args'list

         (* reconstruct *)
         | `LamMany([], { term = `Meta(_) }) ->
             let* args = _PtoList args in
             let* ps = mapM pattcanonRenormalize (head :: args) in
             let* ps = mapM (chasePattcanon []) ps in
             let (head' :: args') = ps in
             let* (head'', argsinfo, typ) =
               (match head'.term with
                   `LamMany(_, { term = `AppMany(hd, _, argsinfo) ;
                                 classifier = typ }) ->
                     return (hd, argsinfo, typ)
                 | _ -> mzero)
             in

             (* check types *)
             let* argstyps = intermlang (fun _ -> gatherArrowTyps head''.classifier) in
             let* _ = if (List.length args' <> List.length argstyps) then mzero else return () in
             let* args' = mapM (uncurry _PtoDyn) (List.combine args' argstyps) in

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
     fun _ -> function [ var ; res ] -> begin
         let* var = pattcanonRenormalize var in
         let* var = chasePattcanon [] var in
         let* (name, idx) = begin
           match var.term with
             `LamMany(_, { term = `AppMany( { term = `Var(`Concrete(name), (`Free, idx)) }, _, _ ) }) ->
               return (name, idx)
           | _ -> mzero
           end
         in
         let* newvar = intermlang (fun _ -> pattOfConstant name idx) in
         pattcanonUnifyFull res newvar
    end | _ -> mzero)
  ;;

  new_builtin_predicate "allconstants" ( (_tList _tDyn) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ res ] -> begin
         let* vars = intermlang (fun _ ->
           let idxs  = increasing !termstate.fvars in
           let names = List.map nameOfFVar idxs in
           let patts = List.map2 pattOfConstant names idxs in
           let dynpatts = List.map _PofDyn patts in
           let list = _PofList _tDyn dynpatts in
           list) in
         pattcanonUnifyFull res vars
     end | _ -> assert false)
  ;;

  new_builtin_predicate "assume_get" ( ~* "A" **> (_tList _tClause) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; unif ] -> begin

        let* pred = pattcanonRenormalize pred in
        let* pred = chasePattcanon [] pred in

        match pred.term with
            `LamMany(_, body) ->
                let idx  =   headPredicate body in
                let* env = getenv in
                let cs   =   try Termlangcanon.IMap.find idx env.retemp_constr_for_pred with Not_found -> [] in
                let* cs' = inmonad ~statewrite:true (fun _ -> List.map (pattneutToCanon % fst % allocateMetas_mutable) cs) in
                pattcanonUnifyFull unif (_PofList ~loc:pred.loc _tClause cs')

    end | _ -> assert false)
  ;;

  new_builtin_predicate "assume_reset" ( ~* "A" **> _tProp **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; { term = `LamMany([], p) } ] -> begin

        let* pred = chasePattcanon [] pred in

        match pred.term with
            `LamMany(_, body) ->
                let idx = headPredicate body in
                let* env' = resetTempConstructors idx in
                inenv env' (demand p)

    end | _ -> assert false)
  ;;

  new_builtin_predicate "rules_get" ( ~* "A" **> (_tList _tClause) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; unif ] -> begin

        let* pred = pattcanonRenormalize pred in
        let* pred = chasePattcanon [] pred in

        match pred.term with
            `LamMany(_, body) ->
                  let idx  =   headPredicate body in
                  let* cs = findConstructors idx in
                  let* cs' = inmonad ~statewrite:true (fun _ -> List.map (pattneutToCanon % fst % allocateMetas_mutable) cs) in
                  pattcanonUnifyFull unif (_PofList ~loc:pred.loc _tClause cs')

    end | _ -> assert false)
  ;;

  new_builtin_predicate "rules_get_applicable" ( ~* "A" **> (_tList _tClause) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; unif ] -> begin

        let* pred = pattcanonRenormalize pred in
        let* pred = chasePattcanon [] pred in

        match pred.term with
            `LamMany(_, body) ->
                  let idx  =   headPredicate body in
                  let* cs = findConstructors idx in
                  let* state = getbacktrackstate in
                  let* csAppl = mapM (fun c ->
                                                let* applies = constructorApplies state body c in
                                                return (if applies then Some c else None)) cs
                  in
                  let cs'  = List.filter_map identity csAppl in
                  let* cs'' = inmonad ~statewrite:true (fun _ -> List.map (pattneutToCanon % fst % allocateMetas_mutable) cs') in
                  pattcanonUnifyFull unif (_PofList ~loc:pred.loc _tClause cs'')

    end | _ -> assert false)
  ;;

  new_builtin_predicate "assume_get_applicable" ( ~* "A" **> (_tList _tClause) **> _tProp )
    (let open RunCtx.Monad in
     fun _ -> function [ pred ; unif ] -> begin

        let* pred = pattcanonRenormalize pred in
        let* pred = chasePattcanon [] pred in

        match pred.term with
            `LamMany(_, body) ->
                let idx  =   headPredicate body in
                let* env = getenv in
                let cs   =   try Termlangcanon.IMap.find idx env.retemp_constr_for_pred with Not_found -> [] in
                let* state = getbacktrackstate in
                let* csAppl = mapM (fun c ->
                                              let* applies = constructorApplies state body c in
                                              return (if applies then Some c else None)) cs
                in
                let cs'  = List.filter_map identity csAppl in
                let* cs'' = inmonad ~statewrite:true (fun _ -> List.map (pattneutToCanon % fst % allocateMetas_mutable) cs') in
                pattcanonUnifyFull unif (_PofList ~loc:pred.loc _tClause cs'')

    end | _ -> assert false)
  ;;

  new_builtin_predicate "isunif" ( ~* "A" **> _tProp )
    (fun _ -> function [ p ] -> begin
      (let open RunCtx.Monad in
         let* state = getstate in
         let* p = pattcanonRenormalize p in
         let* p = chasePattcanon [] p in
         let* _ = setstate state in
         let isunif = match p.term with `LamMany([], { term = `Meta _ }) -> true | _ -> false in
         moneOrMzero isunif)
      end | _ -> assert false)
  ;;

  new_builtin_predicate "isconst" ( ~* "A" **> _tProp )
    (fun _ -> function [ p ] ->
      (let open RunCtx.Monad in
         let* state = getstate in
         let* p = pattcanonRenormalize p in
         let* p = chasePattcanon [] p in
         let* _ = setstate state in
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
         let* state = getstate in
         let* p = pattcanonRenormalize p in
         let* p = chasePattcanon [] p in
         let* _ = setstate state in
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
         let* state = getstate in
         let* p = pattcanonRenormalize p in
         let* p = chasePattcanon [] p in
         let* _ = setstate state in
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
         let* state = getstate in
         let* p = pattcanonRenormalize p in
         let* p = chasePattcanon [] p in
         let* _ = setstate state in
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
         let* state = getstate in
         let* p = pattcanonRenormalize p in
         let* p = chasePattcanon [] p in
         let* _ = setstate state in
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
     fun _ -> function [ term ; index ; args ] -> begin
       let* term = pattcanonRenormalize term in
       let* term = chasePattcanon [] term in
       match term.term with

         (* deconstruct *)
         | `LamMany([], { term = `Meta(_, idx, `Subst(args', _, args'info, _), _) }) ->

            let* _ = pattcanonUnifyFull index (pattcanonInt (Big_int.of_int idx)) in
            let args' = List.map (fun e -> _PofDyn ~loc:e.loc e) args' in
            let args'list = _PofList ~loc:term.loc _tDyn args' in
            pattcanonUnifyFull args args'list

         | _ -> mzero
    end | _ -> assert false)
  ;;

  new_builtin_predicate "recomposeunif" ( ( ~* "A" ) **> (_tList _tDyn) **> ( ~* "A" ) **> _tProp)
    (let open RunCtx.Monad in
     fun _ -> function [ term ; args ; result ] -> begin
       let* term = pattcanonRenormalize term in
       let* term = chasePattcanon [] term in
       match term.term with

         (* reconstruct *)
         | `LamMany([], ({ term = `Meta(s, idx, `Subst(_, _, argsinfo, names), typ) } as neut)) ->
             let* args = _PtoList args in
             let* ps = mapM pattcanonRenormalize args in
             let* ps = mapM (chasePattcanon []) ps in

             (* check types *)
             let* argstyps = intermlang (fun _ -> gatherArrowTyps typ) in
             let* _ = if (List.length ps <> List.length argstyps) then mzero else return () in
             let* args' = mapM (uncurry _PtoDyn) (List.combine ps argstyps) in

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
     fun _ -> function [ term ; level ] -> begin
       let* term = pattcanonRenormalize term in
       let* term = chasePattcanon [] term in
       match term.term with

         (* deconstruct *)
         | `LamMany([], { term = `Meta(m1) }) ->

             let* lvl = getMetaLevel (metaindex m1) in
             pattcanonUnifyFull level (pattcanonInt (Big_int.of_int lvl)) ;

         | _ -> mzero
    end | _ -> assert false)
  ;;

  let ensure_concrete_type (p : pattcanon) : unit RunCtx.Monad.m =
    let open RunCtx.Monad in
      let* t = intermlang (fun _ -> chaseType p.classifier) in
      let b = match t.term with `TVar(_, Some (`Free, _), _) -> true | _ -> false in
      if b then return () else (Printf.printf "wrong call to external predicate expecting concrete type\n"; mzero)

  ;;

  exception MonotypUninstantiatedTMetas;;
  new_builtin_predicate "monotyp" ( ( ~* "A" ) **> _tProp)
  (fun _ -> fun [ e ] ->
    (let open RunCtx.Monad in
     let* e = pattcanonRenormalize e in
     let* p = chasePattcanon ~deep:true [] e in
     let* state = getbacktrackstate in
     let* b = intermlang (fun _ ->
              try
                let p' =
                 p |> pattcanonToExpr 0
                   |> chaseTypesInExpr ~replaceUninst:false ~metasAreFine:true
                in
                ignore(traverseTypeDeep
                        ~uninstantiatedMeta:(fun _ -> raise MonotypUninstantiatedTMetas)
                        p'.classifier);
                true
               with MonotypUninstantiatedTMetas -> false) in
     let* _ = setstate state in
     moneOrMzero b))
  ;;

  new_builtin_predicate "typstring" ( ( ~* "A" ) **> _tString **> _tProp)
  (fun _ -> fun [ e ; s ] ->
    (let open RunCtx.Monad in
     let* e = pattcanonRenormalize e in
     let* p = chasePattcanon ~deep:true [] e in
     let* state = getbacktrackstate in
     let* p' = intermlang (fun _ ->
                let p' =
                 p |> pattcanonToExpr 0
                   |> chaseTypesInExpr ~replaceUninst:false ~metasAreFine:true
                in
                chaseTypeDeep
                        ~metasAreFine:true
                        ~replaceUninst:true
                        p'.classifier ();
                p') in
     let* _ = setstate state in
     (let res = Printf.ksprintf2 (fun s -> s) "%a" Typ.print p'.classifier in
      pattcanonUnifyFull s (_PofString ~loc:e.loc res))))
  ;;

  new_builtin_predicate "statehash" ( _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ s ] ->
    let* metaidx = (match s.term with
         | `LamMany([], { term = `Meta(_, idx, _, _) }) ->
            return idx
         | _ -> mzero) in
    let* statehash = inmonad ~statewrite:false (fun _ ->
      let inp = !UChannel.input_statehash in
      let mt = Hashtbl.hash metaidx in
      let root =
        match !tempstate.rsroot_query with
          Some p -> (match p.loc with
                       Some l -> (let open UChannel in Hashtbl.hash l.startloc.offset)
                     | _ -> 0)
        | _ -> failwith "statehash should always be within the context of a queryGoal?"
      in
      (* we need three components: the input so far, the query we're at,
         and a distinct point within that query. The current metavariable should provide
         that last one. *)
      inp + mt + root) in
    let statehash = string_of_int statehash in
    pattcanonUnifyFull s (_PofString statehash ~loc:s.loc))
  end;;

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
               ifte (
                       let* b = intermlang(fun _ -> typUnifyBool ~allow_instantiation:false p.classifier output.classifier) in
                       moneOrMzero b)
                    (fun () ->
                       let* level = getMetaLevel (metaindex m1) in
                       return (combine cur (Some (level, p))))
                    (lazy(foldM auxcanon cur (metasubstmain m1)))
         | `AppMany(hd, args, _) ->
             foldM auxcanon cur args
       and auxcanon cur (p : pattcanon) =
         match p.term with
           `LamMany(lamsinfo, p) -> auxneut cur p
       in
         let* _ = mapM ensure_concrete_type [ input ; output ] in
         let* p = chasePattcanon ~deep:true [] input in
         let* p = (match p.term with `LamMany([], p) -> return p | _ -> mzero) in
         let* unif = auxneut None p in
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
             (
                let visited = ISet.add uvar visited in
                let tovisit_set = ISet.remove uvar tovisit_set in
                let* cs = getConstraints uvar in
                let* cs' = mapM (fun elm ->
                              match elm with
                                `UnifCanon(bound, p1, p2) ->
                                 let* state = getbacktrackstate in
                                 let* p1 = chasePattcanon bound p1 in
                                 let* p2 = chasePattcanon bound p2 in
                                 let* _ = setstate state in
                                 return (List.filter_map getmetaindexcanon [ p1 ; p2 ])
                              | `Unif(bound, p1, p2) ->
                                 let* state = getbacktrackstate in
                                 let* p1 = chasePattneut bound p1 in
                                 let* p2 = chasePattneut bound p2 in
                                 let* _ = setstate state in
                                 return (List.filter_map getmetaindexneut [ p1 ; p2 ])
                              | _ -> return []) cs
                in
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
         let* _ = mapM ensure_concrete_type [ term ; meta ] in
         let* p = chasePattcanon ~deep:true [] term in
         let* meta = chasePattcanon ~deep:true [] meta in
         let* uvar = (match getmetaindexcanon meta with Some i -> return i | _ -> mzero) in
         let* uvars = chaseWithConstraints uvar in
         let* p = (match p.term with `LamMany([], p) -> return p | _ -> mzero) in
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


let exprRemoveUnresolved (metanames: string list) (e : expr) : exprU =

  let currentNames = ref (StringSet.of_list metanames) in
  let metaToName = ref (IMap.empty: string IMap.t) in
  let registerMeta s i =
    currentNames := StringSet.add s !currentNames;
    metaToName := IMap.add i s !metaToName
  in

  let rec eaux e =
    let e = { e with classifier = taux e.classifier } in
    match e.term with
    | `Var(`Concrete(s), (`Meta, i)) ->
        let s =
          if IMap.mem i !metaToName
          then IMap.find i !metaToName
          else begin
              let s = if s = "" then "X" else s in
              let s =
                if StringSet.mem s !currentNames
                then s ^ "~" ^ (string_of_int i)
                else s
              in
              registerMeta s i;
              s
            end
        in
        { e with term = `Var(`Concrete(s), None) }
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

exception StagingError of exprU;;

let getQueryResult (t : typ) (code : exprU) : exprU RunCtx.Monad.m =

  let open RunCtx.Monad in
    let* code = intermlang (let code' = mkAnnot ~loc:code.loc (fun _ -> code) (t **> _tProp) in
                           mkApp ~loc:code.loc code' (mkVar "Result~~")) in
    let* metas = ifte (queryGoal ~print:false code) (fun x -> return (Some x))
      (lazy(raise (StagingError(code))))
    in
    let* metanames = intermlang allMetaNames in
    let* result = (match metas with Some metas -> intermlang (fun _ ->
      let result = List.assoc "Result~~" metas in
      let result =
        try
          result |> pattcanonToExpr (-1) |> chaseTypesInExpr ~replaceUninst:true ~metasAreFine:true |>
                    alphaSanitize |> exprRemoveUnresolved metanames
        with NewVarUsed -> assert false
      in
      Some result) | None -> return None) in
    let* state = getstate in
    let* _ = setstate (clearRunMetas state) in
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

let rec doCommand loc (e : exprU) : unit RunCtx.Monad.m =

  let open RunCtx.Monad in
  let hd, args = ExprU.gatherApp e in
  let postCleanupMetas e =
      let* _ = e in
      let* state = getstate in
      setstate (clearRunMetas state)
  in
  postCleanupMetas begin
  match hd.term, args with

  | `Var(_, Some (`Free, idx)), [ clause ] when idx = _eiCmdNewClause ->

    let _ = if !_DEBUG_STAGING then Printf.printf "new clause %a\n" (ExprU.print ~debug:true) clause in
    let clause = { clause with loc = loc } in
    defineClause clause

  | `Var(_, Some (`Free, idx)), [ { term = `Const(o) } ; typterm ] when idx = _eiCmdNewTerm ->

    let _ = if !_DEBUG_STAGING then Printf.printf "new term %s : %a\n" (Obj.obj o) Typ.print typterm.classifier in
    let typ = { typterm.classifier with loc = loc } in
    intermlang (fun _ -> typedecl (Obj.obj o) typ () |> ignore)

  | `Var(_, Some (`Free, idx)), [ list ] when idx = _eiCmdMany ->

      let* _ = mapM (doCommand loc) (_EUtoList list) in
      return ()

  | `Var(_, Some (`Free, idx)), [ code ] when idx = _eiCmdStage ->

      let code = { code with loc = loc } in
      let* cmd = getQueryResult _tCmd code in
      doCommand loc cmd

  | `Var(_, Some (`Free, idx)), [] when idx = _eiCmdNone ->

    return ()

  | `Var(_, Some (`Free, idx)), [ query ] when idx = _eiCmdQuery ->

    let query = { query with loc = loc } in
    ifte (queryGoal ~print:true query) (fun _ -> return ()) (lazy(return ()))

  | _ -> mzero
  end

;;


let doStagedCommand (code : exprU) : unit RunCtx.Monad.m =

  let open RunCtx.Monad in
    let* cmd = getQueryResult _tCmd code in
    ifte (doCommand code.loc cmd) return
      (lazy(Printf.printf "Error in staged code at %s.\n"
              (UChannel.string_of_span code.loc); mzero))

;;


let global_staged_command cmdcode =

  let open RunCtx.Monad in
  globalprolog_do (
                    let* cmdcode = intermlang cmdcode in
                    doStagedCommand cmdcode)

;;

new_builtin_predicate "handle_toplevel_command" ( _tCmd **> _tCmd **> _tProp)
    (let open RunCtx.Monad in
     fun _ -> function [ cmdin ; cmdout ] ->
                pattcanonUnifyFull cmdin cmdout
                     | _ -> assert false)
;;

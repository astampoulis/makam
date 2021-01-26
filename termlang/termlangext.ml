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

open Utils;;
open Batteries;;
open Termlangcanon;;
open Termlangbuiltin;;
open Termlangprolog;;


let new_builtin_predicate_from_functions s t fs =
  let open RunCtx.Monad in
  let isMeta p = match p.term with `LamMany(_, { term = `Meta(_) }) -> true | _ -> false in
  new_builtin_predicate s t
  (fun _ -> fun args ->
    let* args' = mapM (chasePattcanon ~deep:true []) args in
    let f, args, meta =
      let n = List.length args' in
      try
        let (prev, meta, next), i = ExtList.find_partition_index isMeta args' in
        let f = List.nth fs i in
        f, prev ++ next, meta
      with ExtList.NotFoundPartition ->
        List.nth fs (n-1), List.take (n-1) args', List.last args'
    in
    let* res = f args in
    pattcanonUnifyFull meta res)
;;

let _totypinfo t = { term = () ; classifier = t ; loc = None ; extra = DummyExtras.empty () } ;;

let _PtoString (s : pattcanon) = let open RunCtx.Monad in match s.term with `LamMany( _, { term = `AppMany( { term = `Const(o) }, _, _) } ) -> return (Obj.obj o) | _ -> mzero ;;
let _PofString ?(loc = None) s : pattcanon = pattcanonString s ~loc:loc ;;

let _PtoInt (s : pattcanon) : Big_int.t RunCtx.Monad.m = let open RunCtx.Monad in match s.term with `LamMany( _, { term = `AppMany( { term = `Const(o) }, _, _) } ) -> return (Obj.obj o) | _ -> mzero ;;
let _PofInt ?(loc = None) i : pattcanon = pattcanonInt i ~loc:loc ;;

let _PtoList  (xs : pattcanon) : pattcanon list RunCtx.Monad.m =
  let open RunCtx.Monad in
  let rec aux s acc =
    let* s = chasePattcanon [] s in
    match s.term with
      `LamMany([], { term = `AppMany( { term = `Var(_, (`Free, idx)) }, [], _) }) when idx = _eiNil ->
        return (List.rev acc)
    | `LamMany([], { term = `AppMany( { term = `Var(_, (`Free, idx)) }, [ hd ; tl ], _) }) when idx = _eiCons ->
        aux tl (hd :: acc)
    | _ -> mzero
  in
  aux xs []
;;
let _PofList ?(loc = None) (t : typ) (xs : pattcanon list) : pattcanon =
  let open RunCtx.Monad in
  let nil : pattcanon = { classifier = _tList t ; loc = loc ; term = `Var( `Concrete("nil"), (`Free, _eiNil) ) ;
                          extra = PattExtras.empty () } |> pattheadToCanon
  in
  let conshead : patthead = { term = `Var( `Concrete("cons"), (`Free, _eiCons) ) ; classifier = t **> _tList t **> _tList t ; loc = loc ; extra = PattExtras.empty () } in
  let cons hd tl : pattcanon =
    let neut =
      { classifier = _tList t ; loc = loc ;
        term = `AppMany( conshead, [ hd ; tl ], [ _tList t **> _tList t |> _totypinfo ; _tList t |> _totypinfo ] ) ;
        extra = PattExtras.empty () }
    in
    { classifier = _tList t ; loc = loc ;
      term = `LamMany([], neut) ; extra = PattExtras.empty () }
  in
  List.fold_right cons xs nil
;;

let _PtoBool (x : pattcanon) : bool RunCtx.Monad.m =
  let open RunCtx.Monad in
     let* x = chasePattcanon [] x in
     match x.term with
         `LamMany([], { term = `AppMany( { term = `Var(_, (`Free, idx)) }, [], _) }) when idx = _eiTrue -> return true
       | `LamMany([], { term = `AppMany( { term = `Var(_, (`Free, idx)) }, [], _) }) when idx = _eiFalse -> return false
;;

let _PofBool ?(loc = None) (x : bool) : pattcanon =
  let open RunCtx.Monad in
  let ptrue : pattcanon = { classifier = _tBool ; loc = loc ;
                            term = `Var( `Concrete("true"), (`Free, _eiTrue) ) ;
                            extra = PattExtras.empty () } |> pattheadToCanon
  in
  let pfals : pattcanon = { classifier = _tBool ; loc = loc ;
                            term = `Var( `Concrete("false"), (`Free, _eiFalse) ) ;
                            extra = PattExtras.empty () } |> pattheadToCanon
  in
  if x then ptrue else pfals
;;

let _PtoDyn (d : pattcanon) (t : typ) : pattcanon RunCtx.Monad.m =
  let open RunCtx.Monad in
  match d.term with
      `LamMany([], { term = `AppMany( { term = `Var(_, (`Free, idx)) }, [ term ], _) }) when idx = _eiDyn ->
          let* b = inmonad ~statewrite:true (fun _ -> typUnifyBool t term.classifier) in
          let* _ = moneOrMzero b in
          return term
    | _ -> mzero
;;

let _PofDyn ?(loc = None) (x : pattcanon) : pattcanon =
  let open RunCtx.Monad in
  let t = x.classifier in
  let dynhead : patthead = { term = `Var(`Concrete("dyn"), (`Free, _eiDyn)); classifier = t **> _tDyn ; loc = loc ; extra = PattExtras.empty () } in
  let dyn e : pattcanon =
    let neut =
      { classifier = _tDyn ; loc = loc ; extra = PattExtras.empty () ;
        term = `AppMany(dynhead, [ e ], [ _tDyn |> _totypinfo ]) }
    in
    { classifier = _tDyn ; loc = loc ; extra = PattExtras.empty () ;
      term = `LamMany([], neut) }
  in
  dyn x
;;

(* ---------
   Integers.
   --------- *)
new_builtin_predicate_from_functions "plus" ( _tInt **> _tInt **> _tInt **> _tProp ) begin
  let open RunCtx.Monad in
  let convertfunc f [ i1 ; i2 ] =
      let* i1' = _PtoInt i1 in
      let* i2' = _PtoInt i2 in
      let res = f i1' i2' in
      return (_PofInt res ~loc:i1.loc)
  in
  [ (* Meta, Const, Const *)
    convertfunc (fun b res -> Big_int.sub res b);

    (* Const, Meta, Const *)
    convertfunc (fun a res -> Big_int.sub res a);

    (* Const, Const, Meta *)
    convertfunc (fun a b -> Big_int.add a b) ]
end;;


new_builtin_predicate "mult" ( _tInt **> _tInt **> _tInt **> _tProp ) begin

  let open RunCtx.Monad in
  let isMeta t = match t.term with `LamMany( _, { term = `Meta(_) } ) -> true | _ -> false in
  (fun _ -> fun [ i1; i2; res ] ->
    let* i1' = chasePattcanon [] i1 in
    let* i2' = chasePattcanon [] i2 in
    let* res' = chasePattcanon [] res in
    if isMeta i1' || isMeta i2' then mzero
    else (
            let* i1'' = _PtoInt i1' in
            let* i2'' = _PtoInt i2' in
            pattcanonUnifyFull res' (_PofInt (Big_int.mul i1'' i2'') ~loc:res.loc)))

end;;

new_builtin_predicate "div" ( _tInt **> _tInt **> _tInt **> _tInt **> _tProp ) begin

  let open RunCtx.Monad in
  let isMeta t = match t.term with `LamMany( _, { term = `Meta(_) } ) -> true | _ -> false in
  (fun _ -> fun [ i1; i2; quo; rem ] ->
    let* i1' = chasePattcanon [] i1 in
    let* i2' = chasePattcanon [] i2 in
    let* quo' = chasePattcanon [] quo in
    let* rem' = chasePattcanon [] rem in
    if isMeta i1' || isMeta i2' then mzero
    else (
            let* i1'' = _PtoInt i1' in
            let* i2'' = _PtoInt i2' in
            try begin
                let (q'', r'') = Big_int.quomod_big_int i1'' i2'' in
                let* _ = pattcanonUnifyFull quo' (_PofInt q'' ~loc:quo.loc) in
                let* _ = pattcanonUnifyFull rem' (_PofInt r'' ~loc:rem.loc) in
                return ()
              end
            with _ -> mzero))

end;;

new_builtin_predicate "lessthan" ( _tInt **> _tInt **> _tBool **> _tProp ) begin

  let open RunCtx.Monad in
  let isMeta t = match t.term with `LamMany( _, { term = `Meta(_) } ) -> true | _ -> false in
  (fun _ -> fun [ i1; i2; res ] ->
    let* i1' = chasePattcanon [] i1 in
    let* i2' = chasePattcanon [] i2 in
    if isMeta i1' || isMeta i2' then mzero
    else (
            let* i1'' = _PtoInt i1' in
            let* i2'' = _PtoInt i2' in
            pattcanonUnifyFull res (_PofBool (Big_int.lt_big_int i1'' i2'') ~loc:i1.loc)))

end;;

(* ---------
   Strings.
   --------- *)

builtin_enter_module "string" ;;

new_builtin_predicate_from_functions "append" ( _tString **> _tString **> _tString **> _tProp) begin
  let open RunCtx.Monad in
  let convertfunc f [ s1 ; s2 ] =
      let* s1' = _PtoString s1 in
      let* s2' = _PtoString s2 in
      let res = f s1' s2' in
      match res with
        Some(s) -> return (_PofString s ~loc:s1.loc)
      | None -> mzero
  in
  [ (* Meta, Const, Const *)
    convertfunc (fun strTL strFULL ->
      if String.ends_with strFULL strTL then
        let strHD = String.sub strFULL 0 (String.length strFULL - String.length strTL) in
        Some strHD
      else
        None);

    (* Const, Meta, Const *)
    convertfunc (fun strHD strFULL ->
      if String.starts_with strFULL strHD then
        let strTL = String.sub strFULL (String.length strHD) (String.length strFULL - String.length strHD) in
        Some strTL
      else
        None) ;

    (* Const, Const, Meta *)
    convertfunc (fun strHD strTL -> Some (strHD ^ strTL)) ]
end
;;

new_builtin_predicate "headtail" ( _tString **> _tString **> _tString **> _tProp) begin
  let open RunCtx.Monad in
  let isMeta t = match t.term with `LamMany( _, { term = `Meta(_) } ) -> true | _ -> false in
  (fun _ -> fun [ i; hd; tl ] ->
    let* i' = chasePattcanon [] i in
    let* hd' = chasePattcanon [] hd in
    let* tl' = chasePattcanon [] tl in
    if (not (isMeta i')) then
      (let* is = _PtoString i' in
       let* _ = if String.is_empty is then mzero else return () in
       let* _ = pattcanonUnifyFull hd' (_PofString (String.head is 1) ~loc:i.loc) in
       let* _ = pattcanonUnifyFull tl' (_PofString (String.tail is 1) ~loc:i.loc) in
       return ())
    else if (isMeta i' && not(isMeta hd') && not(isMeta tl')) then
      (let* hds = _PtoString hd' in
       let* tls = _PtoString tl' in
       pattcanonUnifyFull i' (_PofString (hds ^ tls) ~loc:hd.loc))
    else mzero)
end
;;

new_builtin_predicate "initlast" ( _tString **> _tString **> _tString **> _tProp) begin
  let open RunCtx.Monad in
  let isMeta t = match t.term with `LamMany( _, { term = `Meta(_) } ) -> true | _ -> false in
  (fun _ -> fun [ i; init; last ] ->
    let* i' = chasePattcanon [] i in
    let* init' = chasePattcanon [] init in
    let* last' = chasePattcanon [] last in
    if (not (isMeta i')) then
      (let* is = _PtoString i' in
       let* _ = if String.is_empty is then mzero else return () in
       let* _ = pattcanonUnifyFull init' (_PofString (String.slice ~last:(-1) is) ~loc:i.loc) in
       let* _ = pattcanonUnifyFull last' (_PofString (String.slice ~first:(-1) is) ~loc:i.loc) in
       return ())
    else if (isMeta i' && not(isMeta init') && not(isMeta last')) then
      (
         let* inits = _PtoString init' in
         let* lasts = _PtoString last' in
         pattcanonUnifyFull i' (_PofString (inits ^ lasts) ~loc:init.loc))
    else mzero)
end
;;

new_builtin_predicate "split_at_first" ( _tString **> _tString **> _tString **> _tString **> _tProp) begin
  let open RunCtx.Monad in
  let isMeta t = match t.term with `LamMany( _, { term = `Meta(_) } ) -> true | _ -> false in
  (fun _ -> fun [ sep; full; splithd; splittl ] ->
    let* sep' = chasePattcanon [] sep in
    let* full' = chasePattcanon [] full in
    let* splithd' = chasePattcanon [] splithd in
    let* splittl' = chasePattcanon [] splittl in
    if (isMeta sep') then
      mzero
    else if (not (isMeta full')) then
      (
         let* seps = _PtoString sep' in
         let* fulls = _PtoString full' in
         let* (shd, stl) =
           (try return (String.split fulls seps) with Not_found -> mzero)
         in
         let* _ =
           pattcanonUnifyFull splithd' (_PofString shd ~loc:full.loc)
         in
         pattcanonUnifyFull splittl' (_PofString stl ~loc:full.loc))
    else if (isMeta full' && not(isMeta splithd') && not(isMeta splittl')) then
      (
         let* seps = _PtoString sep' in
         let* hds = _PtoString splithd' in
         let* tls = _PtoString splittl' in
         pattcanonUnifyFull full' (_PofString (hds ^ seps ^ tls) ~loc:splithd.loc))
    else mzero)
end
;;


new_builtin_predicate_from_functions "explode" (_tString **> _tList _tString **> _tProp) begin
  let open RunCtx.Monad in
  [ (function [ ls ] ->
        let* ls' = _PtoList ls in
        let* ls'' = mapM _PtoString ls' in
        let s = String.concat "" ls'' in
        return (_PofString ~loc:ls.loc s));
    (function [ s ] ->
        let* s' = _PtoString s in
        let open UChannel in
        let span = match s.loc with Some { startloc = loc } -> Some loc | None -> None in
        let stream = UChannel.from_string ?initloc:span s' in
        let s'' = stream |> UChannel.map
                            (fun chan c -> UString.implode [c] |> UString.to_string
                                           |> _PofString ~loc:(UChannel.mk_span (UChannel.loc chan) (UChannel.loc chan)))
        in
        return (_PofList _tString s'' ~loc:s.loc)
    ) ]
end
;;


new_builtin_predicate "capitalize" ( _tString **> _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ str; res ] ->
    let* str = chasePattcanon [] str in
    let* str' = _PtoString str in
    pattcanonUnifyFull res (_PofString (String.capitalize str') ~loc:str.loc))
end;;

new_builtin_predicate "uppercase" ( _tString **> _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ str; res ] ->
    let* str = chasePattcanon [] str in
    let* str' = _PtoString str in
    pattcanonUnifyFull res (_PofString (String.uppercase str') ~loc:str.loc))
end;;

new_builtin_predicate "lowercase" ( _tString **> _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ str; res ] ->
    let* str = chasePattcanon [] str in
    let* str' = _PtoString str in
    pattcanonUnifyFull res (_PofString (String.lowercase str') ~loc:str.loc))
end;;

new_builtin_predicate "contains" ( _tString **> _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ str1; str2 ] ->
    let* str1 = chasePattcanon [] str1 in
    let* str1' = _PtoString str1 in
    let* str2 = chasePattcanon [] str2 in
    let* str2' = _PtoString str2 in
    moneOrMzero (String.exists str1' str2'))
end;;

let readFileAsString ?(statehash_update = true) filename =
  let chan = UChannel.from_filename ~statehash_update:statehash_update filename in
  let startLoc = UChannel.loc chan in
  let (s, chan') =
    let store = ref [] in
    let rec aux c =
      match UChannel.get_one c with
        None -> (!store |> List.rev |> UString.implode, c)
      | Some (hd, c') -> store := (hd :: !store); aux c'
    in
    aux chan
  in
  let endLoc = UChannel.loc chan' in
  let span = UChannel.mk_span startLoc endLoc in
  _PofString (UString.to_string s) ~loc:span
;;

new_builtin_predicate "readfile" ( _tString **> _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ filename; content ] ->
    let* filename = chasePattcanon [] filename in
    let* filename = _PtoString filename in
    let* contentString = (try return (readFileAsString filename) with _ -> mzero) in
    pattcanonUnifyFull content contentString)
end;;

new_builtin_predicate "readcachefile" ( _tString **> _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ filename; content ] ->
    let* filename = chasePattcanon [] filename in
    let* filename = _PtoString filename in
    let* contentString = (
      let res =
        try
          let resolved = Termlangcanon.global_resolve_cache_filename (filename ^ ".makam-cache") in
          return (readFileAsString ~statehash_update:false resolved)
        with _ -> mzero
      in
      res
    ) in
    pattcanonUnifyFull content contentString)
end;;

new_builtin_predicate "writefile" ( _tString **> _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ filename; content ] ->
    let* filename = chasePattcanon [] filename in
    let* filename = _PtoString filename in
    let* content = chasePattcanon [] content in
    let* content = _PtoString content in
    try
      let output = File.open_out filename in
      let _ = IO.nwrite output content in
      let _ = IO.close_out output in
      return ()
    with _ ->
      mzero)
end;;

new_builtin_predicate "writecachefile" ( _tString **> _tString **> _tProp ) begin
  let open RunCtx.Monad in
  (fun _ -> fun [ filename; content ] ->
    match global_get_cache_directory () with
      Some makam_cache_dir -> begin
        let* filename = chasePattcanon [] filename in
        let* filename = _PtoString filename in
        let* content = chasePattcanon [] content in
        let* content = _PtoString content in
        let* _ = (try
                 if Sys.is_directory makam_cache_dir then return () else mzero
               with _ ->
                 (try
                    Unix.mkdir makam_cache_dir 0o775; return ()
                  with _ -> mzero)) in
        try
          let output = File.open_out (makam_cache_dir ^ "/" ^ filename ^ ".makam-cache") in
          let _ = IO.nwrite output content in
          let _ = IO.close_out output in
          return ()
        with _ ->
          mzero
      end
    | None -> mzero)
end;;


builtin_leave_module ();;


(* --------------
   Character classes.
   -------------- *)
let _ =
  let new_char_class s f =
    (let open RunCtx.Monad in
    let isMeta t = match t.term with `LamMany( _, { term = `Meta(_) } ) -> true | _ -> false in
    new_builtin_predicate s (_tString **> _tProp)
    (fun _ -> fun [ c ] ->
      let* c' = chasePattcanon ~deep:true [] c in
      if isMeta c' then mzero
      else (let* c'' = _PtoString c' in
            let c'' = UString.gethd (UString.of_string c'') in
            moneOrMzero (f c''))))
  in
  ignore(new_char_class "char_latin1" (fun c -> try (ignore (UChar.char_of c); true) with _ -> false));
  new_char_class "char_letter" (fun c -> match UString.category c with
    | `Ll | `Lm | `Lo | `Lt | `Lu -> true | _ -> false)
;;


(* Printing. *)
new_builtin_predicate "print" ( ~* "A" **> _tProp )
  (fun _ -> fun [ e ] ->
    (let open RunCtx.Monad in
     let* e = pattcanonRenormalize e in
     let* p = chasePattcanon ~deep:true [] e in
     let _ = Printf.printf "%a\n%!" Pattcanon.alphaSanitizedPrint p in
     return ()))
;;

new_builtin_predicate "tostring" ( ~* "A" **> _tString **> _tProp )
  (fun _ -> fun [ e ; s ] ->
    (let open RunCtx.Monad in
     let* e = pattcanonRenormalize e in
     let* p = chasePattcanon ~deep:true [] e in
     let res = Printf.sprintf "%a" Pattcanon.alphaSanitizedPrint p in
     pattcanonUnifyFull s (_PofString ~loc:e.loc res)))
;;

new_builtin_predicate "tostring_qualified" ( ~* "A" **> _tString **> _tProp )
  (fun _ -> fun [ e ; s ] ->
    (let open RunCtx.Monad in
     let* e = pattcanonRenormalize e in
     let* p = chasePattcanon ~deep:true [] e in
     let res = Printf.sprintf "%a" Pattcanon.alphaSanitizedQualifiedPrint p in
     pattcanonUnifyFull s (_PofString ~loc:e.loc res)))
;;

new_builtin_predicate "print_string" ( _tString **> _tProp )
  (fun _ -> fun [ e ] ->
    (let open RunCtx.Monad in
     let* e = pattcanonRenormalize e in
     let* p = chasePattcanon ~deep:true [] e in
     let* s = _PtoString p in
     let _ = Printf.printf "%s%!" s in
     return ()))
;;

new_builtin_predicate "cheapprint" ( _tInt **> ~* "A" **> _tProp )
  (fun _ -> fun [ depth ; e ] ->
    (let open RunCtx.Monad in
     let* e = pattcanonRenormalize e in
     let* p = chasePattcanon ~deep:true [] e in
     let* depth = chasePattcanon ~deep:true [] depth in
     let* depth = _PtoInt depth in
     let* _ = inmonad ~statewrite:false (fun _ -> Printf.printf "%a\n%!" (CheapPrint.canondepth (Big_int.to_int depth)) p) in
     return ()))
;;

new_builtin_predicate "print_current_metalevel" ( _tProp )
  (fun _ -> fun [] ->
    (let open RunCtx.Monad in
       let* env = getenv in
       let _ = Printf.printf "current metalevel: %a\n" (List.print (Pair.print CheapPrint.name Typ.print)) env.renvars  in
       return ()))
;;


(* -------------
   Local debugging.
   ------------- *)
new_builtin_predicate "debug" ( _tProp  **> _tProp )
  (fun _ -> fun [ p ] ->
    let open RunCtx.Monad in
      let* _ = return () in
      let prev = !_DEBUG_DEMAND in
      let _ = _DEBUG_DEMAND := true in
      let p = match p.term with `LamMany([], p) -> p | _ -> assert false in
      ifte (try demand p with e -> (_DEBUG_DEMAND := prev; raise e))
           (fun _ -> _DEBUG_DEMAND := prev; return ())
           (lazy(
              let* _ = return () in
              let _ = _DEBUG_DEMAND := prev in
              mzero)) )
;;

new_builtin_predicate "debugfull" ( _tProp  **> _tProp )
  (fun _ -> fun [ p ] ->
    let open RunCtx.Monad in
      let* _ = return () in
      let prev = !_DEBUG in
      let _ = _DEBUG := true in
      let p = match p.term with `LamMany([], p) -> p | _ -> assert false in
      ifte (try demand p with e -> (_DEBUG := prev; raise e))
           (fun _ -> _DEBUG := prev; return ())
           (lazy(
              let* _ = return () in
              let _ = _DEBUG := prev in
              mzero)))
;;

new_builtin_predicate "debugtypes" ( _tProp  **> _tProp )
  (fun _ -> fun [ p ] ->
    let open RunCtx.Monad in
      let* _ = return () in
      let prev = !_DEBUG_TYPES in
      let _ = _DEBUG_TYPES := true in
      let p = match p.term with `LamMany([], p) -> p | _ -> assert false in
      ifte (try demand p with e -> (_DEBUG_TYPES := prev; raise e))
           (fun _ -> _DEBUG_TYPES := prev; return ())
           (lazy(
              let* _ = return () in
              let _ = _DEBUG_TYPES := prev in
              mzero)) )
;;

new_builtin_predicate "trace" ( (~* "A") **> _tProp **> _tProp )
  (fun _ -> fun [ g ; cont ] ->
    let open RunCtx.Monad in

      let* g' = pattcanonRenormalize g in
      let* cont = pattcanonRenormalize cont in
      let cont = match cont.term with `LamMany([], cont) -> cont | _ -> assert false in

      let* idx = (match g'.term with
            `LamMany(_, ({ classifier = { term = `TVar(_, tidx, _) } } as p))
              when tidx = _tiProp ->
              return (headPredicate p)
          | _ -> mzero)  in

      let* oldval = inmonad (fun () -> isTraced_mutable idx) in
      let* _ =
        inmonad ~statewrite:true (fun () -> setTracedIndex_mutable true idx)
      in

      ifte
        (try
           let* r = demand cont in
           return (`Left r)
         with e -> return (`Right e))
        (fun res ->
          let* _ =
            inmonad ~statewrite:true (fun () -> setTracedIndex_mutable oldval idx)
          in
          return (reflectexn res))
        (lazy(
             let* _ = inmonad ~statewrite:true (fun () -> setTracedIndex_mutable oldval idx)
             in
             mzero)))
;;


(* Locations. *)
(* ---------- *)
(* quite buggy for the time being *)

let _PtoLoc (s : pattcanon) : UChannel.span RunCtx.Monad.m = let open RunCtx.Monad in match s.term with `LamMany( _, { term = `AppMany( { term = `Const(o) }, _, _) } ) -> return (Obj.obj o) | _ -> mzero ;;
let _PofLoc ?(loc = None) s : pattcanon = pattcanonLoc s ~loc:loc ;;

new_builtin_predicate "locget" ( ~* "A" **> _tLoc **> _tProp)
  (let open RunCtx.Monad in
   fun _ -> fun [ which ; res ] ->
      let* which = pattcanonRenormalize which in
      let* which = chasePattcanon [] which in
      let loc = match which.term with `LamMany([], tm) -> tm.loc | _ -> which.loc in
      pattcanonUnifyFull res (_PofLoc loc))
;;

new_builtin_predicate "locset" ( ~* "A" **> _tLoc **> ~* "A" **> _tProp)
  (let open RunCtx.Monad in
   fun _ -> fun [ which ; loc ; res ] ->
      let* which = pattcanonRenormalize which in
      let* which = chasePattcanon [] which in
      let* loc = chasePattcanon [] loc in
      let* loc = _PtoLoc loc in
      let which' =
        match which.term with
          `LamMany(lamsinfo, body) -> { which with term = `LamMany(lamsinfo, { body with loc = loc }) ; loc = loc }
      in
      pattcanonUnifyFull res which')
;;

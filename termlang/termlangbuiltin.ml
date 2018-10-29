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

open Batteries ;;
open Termlangcanon ;;


let new_builtin_type s =
  let i = builtin_do (typedecl s _tType) in
  let idx = Some (`Free, i) in
  (idx, { term = `TVar(s, idx, []) ; classifier = () ; loc = None ; extra = TypExtras.empty () })
;;

let new_builtin_const_type (type t) s (m : (module Const.ConstType with type t = t)) =
  let i = builtin_do (typedecl s _tType) in
  let idx = Some (`Free, i) in
  let _ = Const.add_builtin_type i (module struct include (val m) end) in
  let mkConst ?(loc = None) (o : t) () : exprU =
    let typ = { term = `TVar(s, idx, []) ; classifier = () ; loc = loc ; extra = TypExtras.empty () } in
    { term = `Const(Obj.repr o) ; classifier = typ ; loc = loc ; extra = ExprExtras.empty () }
  in
  let headConst ?(loc = None) (o : t) =
    let typ = { term = `TVar(s, idx, []) ; classifier = () ; loc = loc ; extra = TypExtras.empty () } in
    { term = `Const(Obj.repr o) ; classifier = typ ; loc = loc ; extra = DummyExtras.empty () }
  in
  let neutConst ?(loc = None) (o : t) =
    let head = headConst ~loc:loc o in
    { term = `AppMany(head, [], []) ;
      classifier = head.classifier ;
      loc = loc ; extra = DummyExtras.empty () }
  in
  let canonConst ?(loc = None) (o : t) =
    let neut = neutConst ~loc:loc o in
    { term = `LamMany([], neut) ;
      classifier = neut.classifier ;
      loc = loc ; extra = DummyExtras.empty () }
  in
  (idx, { term = `TVar(s, idx, []) ; classifier = () ; loc = None ; extra = TypExtras.empty () },
   mkConst, headConst, neutConst, canonConst)
;;

let new_builtin_type_constructor s =
  let i = builtin_do (typedecl s (_tType **> _tType)) in
  let idx = Some (`Free, i) in
  (idx, fun t -> { term = `TVar(s, idx, [t]) ; classifier = () ; loc = None ; extra = TypExtras.empty () })
;;

let new_builtin_type_constructor_binary s =
  let i = builtin_do (typedecl s (_tType **> _tType **> _tType)) in
  let idx = Some (`Free, i) in
  let mkType ?(loc = None) t1 t2 = { term = `TVar(s, idx, [t1; t2]) ; classifier = () ; loc = loc ; extra = TypExtras.empty () } in
  (idx, mkType)
;;

let new_builtin s t =
  let i = builtin_do (typedecl s t) in
  i
;;

let builtin_enter_module m  = builtin_do (enter_module m) ;;
let builtin_leave_module () = builtin_do leave_module;;


let _tiString, _tString, mkString, pattheadString, pattneutString, pattcanonString =
  new_builtin_const_type "string"
  (module struct
    type t = string
    let printer s _ = s |> UString.of_string |> UString.quote |> UString.to_string
    let eq s1 s2 _ _ = (s1 = s2)
  end);;

let _ = builtinStringType := _tString ;;


let _tiInt, _tInt, mkInt, pattheadInt, pattneutInt, pattcanonInt =
  new_builtin_const_type "int" 
  (module struct
    type t = Big_int.big_int
    let printer i _ = Big_int.to_string i
    let eq i1 i2 _ _ = Big_int.equal i1 i2
  end);;

let _tiLoc, _tLoc, mkLoc, pattheadLoc, pattneutLoc, pattcanonLoc =
  new_builtin_const_type "loc"
  (module struct
    type t = UChannel.span
    let printer l _  = UChannel.string_of_span l
    let eq l1 l2 _ _ = l1 == l2
  end);;
    

let _tiList, _tList     = new_builtin_type_constructor "list" ;;
let _eiNil              = new_builtin "nil"  (_tList ( ~* "A" ));;
let _eiCons             = let a = ~* "A" in
                          new_builtin "cons" (a **> _tList a **> _tList a) ;;

let _tiUnit, _tUnit     = new_builtin_type "unit" ;;
let _eiUnit             = new_builtin "unit" _tUnit;;

let _tiBool, _tBool     = new_builtin_type "bool" ;;
let _eiTrue             = new_builtin "true" _tBool ;;
let _eiFalse            = new_builtin "false" _tBool ;;

let _tiTuple, _tTuple   = new_builtin_type_constructor_binary "tuple" ;;
let _eiTuple            = let a = ~* "A" in
                          let b = ~* "B" in
                          new_builtin "tuple" ( a **> b **> _tTuple a b );;

let _tiDyn, _tDyn       = new_builtin_type "dyn" ;;
let _eiDyn              = let a = ~* "A" in
                          new_builtin "dyn" (a **> _tDyn) ;;

let _tiProp, _tProp     = new_builtin_type "prop" ;;
let _tiClause, _tClause = new_builtin_type "clause" ;;

let _eiClause           = new_builtin "clause" (_tProp **> _tProp **> _tClause) ;;
let _eiWhenClause       = new_builtin "whenclause" (_tProp **> _tProp **> _tProp **> _tClause) ;;

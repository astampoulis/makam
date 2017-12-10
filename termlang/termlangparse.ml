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
open Termlangext;;

(* Parsing *)

(* 

This could be in termlangext, but separating it out so that
we avoid a circular dependency between the grammar and termlangext.

*)
  
new_builtin_predicate "fromstring" ( _tString **> ~* "A" **> _tProp )
  (fun _ -> fun [ str; e ] ->
    (let open RunCtx.Monad in
     perform
     str <-- pattcanonRenormalize str ;
     pstr <-- chasePattcanon ~deep:true [] str ;
     s <-- _PtoString pstr ;
     let getExpr =
       try
         Some(Peg.parse_of_string MakamGrammar.parse_lexpr s)
       with _ ->
         None
     in
     match getExpr with
       None -> mzero
     | Some getExpr -> perform
         expr <-- intermlang getExpr.content ;
         p <-- intermlang (fun _ ->
           try
             (* TODO: handling of unification variables is unclear here *)
             Some(withConcreteBoundMode true (fun _ -> typecheck_and_normalize expr) |> fst |> chaseTypesInExpr ~metasAreFine:true ~replaceUninst:false |> exprToPattcanon)
           with _ -> None
         );
         let _ = if (!_DEBUG) then Printf.printf "fromstring:: %s >> %a\n" s (Option.print Pattcanon.print) p in
         match p with Some p -> pattcanonUnifyFull e p | None -> mzero))
;;


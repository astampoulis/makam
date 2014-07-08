open Camlp4 ;;
open Camlp4.PreCast ;;

let myparser : (UChannel.loc -> string -> Obj.t) ref = ref (fun loc s -> Obj.magic s) ;;

let conv_loc _loc =
  let file   = Loc.file_name _loc in
  let lineno = string_of_int (Loc.start_line _loc) in
  let colno  = string_of_int (Loc.start_off _loc - Loc.start_bol _loc) in
  <:expr< let open UChannel in { description = $str:file$ ; charno = $int:colno$ ; lineno = $int:lineno$ ; offset = 0 } >>
;;

let expand_myquot _loc _ s =
  let loc = conv_loc _loc in
  <:expr< Obj.magic (!PegQuote.myparser $loc$ $str:s$) >> ;;

let expand_myquot_stritem _loc _ s =
  let loc = conv_loc _loc in
  <:str_item< Obj.magic (!PegQuote.myparser $loc$ $str:s$) >> ;;

Syntax.Quotation.add "myparser" Syntax.Quotation.DynAst.expr_tag expand_myquot;;
Syntax.Quotation.add "myparser" Syntax.Quotation.DynAst.str_item_tag expand_myquot_stritem;;
Syntax.Quotation.default := "myparser" ;;

let install parsefunc =
  myparser := (fun loc s -> Obj.magic (Peg.parse_of_string ~initloc:loc parsefunc s)) ;;


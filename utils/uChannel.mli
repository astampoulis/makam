open Batteries;;

type loc      = { description : string ; lineno : int ; charno : int ; offset : int } ;;
type realspan = { startloc : loc ; endloc : loc } ;;
type span     = realspan option ;;

val  string_of_loc     : loc -> string ;;
val  string_of_span    : span -> string ;;
val  span_end          : span -> span ;;

val  loc_compare       : loc -> loc -> int ;;
val  mk_span           : loc -> loc -> span ;;
val  combine_span      : span -> span -> span ;;

type t ;;

val  from_filename : string -> t ;;
val  from_string   : ?initloc:loc -> string -> t ;;
val  from_stdin    : unit -> t ;;

val  offset            : t -> int ;;
val  loc               : t -> loc ;;
val  reached_eof       : t -> bool ;;
val  at_eof            : t -> bool ;;

val  current_statehash : int ref;;

val  get_one           : t -> (UChar.uchar * t) option ;;
val  map               : (t -> UChar.uchar -> 'a) -> t -> 'a list ;;
val  flush_to_furthest : t -> t ;;


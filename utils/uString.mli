open Batteries ;;

type t ;;
type ustring = t ;;
val of_ustring       : BatUTF8.t -> t ;;

val of_string        : string -> t;;
val to_string        : t -> string;;
val of_string_unsafe : string -> t ;;
external of_string_unsafe_fast : string * int * int * bool -> ustring = "%identity" ;;

val underlying : t -> BatUTF8.t * BatUTF8.ByteIndex.b_idx * BatUTF8.ByteIndex.b_idx * bool ;;

val is_empty   : t -> bool ;;
val gethd      : t -> UChar.t ;;

val contains   : t -> UChar.t -> bool ;;
val concat     : t list -> t ;;
val compare    : t -> t -> int ;;
val iter       : (UChar.t -> unit) -> t -> unit ;;
val enum       : t -> UChar.t Enum.t ;;
val print      : 'a BatInnerIO.output -> t -> unit ;;
val escaped    : t -> t;;
val quote      : t -> t;;

val implode    : UChar.t list -> t ;;
val explode    : t -> UChar.t list ;;

val append_uchar  : t -> UChar.t -> t ;;
val prepend_uchar : t -> UChar.t -> t ;;
val append_bytes  : t -> string -> t ;;
val prepend_bytes : t -> string -> t ;;

type bidx = int ;;

val mkempty         : int -> int -> t ;;
val look_unsafe     : t -> bidx -> UChar.t ;;
val next_unsafe     : t -> bidx -> bidx ;;
val looknext_unsafe : t -> bidx -> UChar.t * bidx ;;
val safe_offset     : t -> bidx -> bool ;;
val is_end          : t -> bidx -> bool ;;


type general_category_type =
  [ `Cc | `Cf | `Cn | `Co | `Cs | `Ll | `Lm | `Lo | `Lt | `Lu | `Mc | `Me | `Mn | `Nd | `Nl
  | `No | `Pc | `Pd | `Pe | `Pf | `Pi | `Po | `Ps | `Sc | `Sk | `Sm | `So | `Zl | `Zp | `Zs ]

val category        : UChar.t -> general_category_type ;;
val is_whitespace   : UChar.t -> bool ;;
val is_uppercase    : UChar.t -> bool ;;

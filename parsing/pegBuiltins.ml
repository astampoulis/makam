open Batteries;;
open UChar;;
open Utils;;
open PegRuntime;;
open Peg ;;

let rec parse_fastrepV p : unit parser_t =
  fun _memocells _resetmemo ->
    let rec aux input =
      match p false input with
	  Some(_, input') -> aux input'
	| None -> Some( (), input )
    in
    aux
;;

let rec parse_fastrep p =
  fun _memocells _resetmemo ->
    let rec aux acc input =
      match p false input with
	  Some(cur, input') -> aux (cur :: acc) input'
	| None -> Some( List.rev acc, input )
    in
    aux []
;;

updateExternalMemocellsInfo [ "fastrepV", 0 ; "fastrep" , 0 ] ;;

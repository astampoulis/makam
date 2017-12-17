(* Workaround until I find out what's wrong with Ropes
   (large ropes return different length than they should) *)

open Batteries ;;
open UChar ;;

type t = BatUTF8.t * BatUTF8.ByteIndex.b_idx (* byte offset *) * BatUTF8.ByteIndex.b_idx (* byte end *) * bool (* aligned *) ;;
type ustring = t ;;

let of_ustring x = x,
                   BatUTF8.ByteIndex.first,
                   BatUTF8.ByteIndex.of_int_unsafe (String.length (BatUTF8.to_string_unsafe x)),
                   true ;;

let of_string  s = BatUTF8.validate s ;
		   s, BatUTF8.ByteIndex.first, BatUTF8.ByteIndex.of_int_unsafe (String.length (BatUTF8.to_string_unsafe s)),
		   true ;;

let of_string_unsafe x = BatUTF8.of_string_unsafe x, BatUTF8.ByteIndex.first, BatUTF8.ByteIndex.of_int_unsafe (String.length x),
                         false ;;

external of_string_unsafe_fast : string * int * int * bool -> ustring = "%identity" ;;

let ast_of_ustring _loc (s, off, bend, algn) =
  let open Camlp4.PreCast in
  let (s, off, bend, algn) = (s |> BatUTF8.to_string_unsafe |> String.escaped,
			     off |> BatUTF8.ByteIndex.to_int |> string_of_int,
			     bend |> BatUTF8.ByteIndex.to_int |> string_of_int,
			     if algn then "True" else "False") in
  Ast.ExApp (_loc,
      (Ast.ExId (_loc,
           (Ast.IdAcc (_loc, (Ast.IdUid (_loc, "UString")),
              (Ast.IdLid (_loc, "of_string_unsafe_fast")))))),
        (Ast.ExTup (_loc,
           (Ast.ExCom (_loc, (Ast.ExStr (_loc, s)),
              (Ast.ExCom (_loc, (Ast.ExInt (_loc, off)),
                 (Ast.ExCom (_loc, (Ast.ExInt (_loc, bend)),
                    (Ast.ExId (_loc, Ast.IdUid(_loc, algn))))))))))))
  (*
  <:expr< UString.of_string_unsafe ($str:s$, $int:off$, $int:bend$, $int:len$) >>
  *)
;;

let ustring_ast_of_string _loc s =
  ast_of_ustring _loc (of_string s)
;;

let to_string  (x, off, bend, _) =
  String.sub (BatUTF8.to_string_unsafe x) (BatUTF8.ByteIndex.to_int off) (BatUTF8.ByteIndex.to_int bend - BatUTF8.ByteIndex.to_int off) ;;

let print oc (s, off, bend, _) =
  let s' = BatUTF8.to_string_unsafe s in
  for i = BatUTF8.ByteIndex.to_int off to BatUTF8.ByteIndex.to_int bend - 1 do
    BatIO.write oc (String.get s' i)
  done ;;

let compare s1 s2 = Pervasives.compare (to_string s1) (to_string s2) ;;

let iter proc (s, off, bend, _) =
  let off = ref off in
  while !off < bend do
    let u = BatUTF8.ByteIndex.look s !off in
    proc u ;
    off := BatUTF8.ByteIndex.next s !off
  done
;;

let looknext_unsafe (s, bstart, bend, _) off =
  let off = BatUTF8.ByteIndex.of_int_unsafe off in
  BatUTF8.ByteIndex.look s off, BatUTF8.ByteIndex.to_int (BatUTF8.ByteIndex.next s off)
;;

let safe_offset (s, bstart, bend, _) off =
  let bstart' = BatUTF8.ByteIndex.to_int bstart in
  let bend'   = BatUTF8.ByteIndex.to_int bend in
  if off < bstart' || off >= bend' then false
  else (let c = String.get (BatUTF8.to_string_unsafe s) off in
	let i = BatUTF8.length0 (Char.code c) in
	off + i <= bend')
;;

let is_end (_, _, bend, _) off = off == BatUTF8.ByteIndex.to_int bend ;;

let look_unsafe s off = fst (looknext_unsafe s off) ;;
let next_unsafe s off = snd (looknext_unsafe s off) ;;

let is_empty s = not (safe_offset s 0) ;;
let gethd s = if is_empty s then raise (Invalid_argument "UString.gethd on empty string") else look_unsafe s 0 ;;

(* O(n) *)
let rec contains_aux ((s, _, bend, _) as x) off u =
  if off >= bend then false
  else if BatUTF8.ByteIndex.look s off = u then true
  else contains_aux x (BatUTF8.ByteIndex.next s off) u
;;

let contains ((s, off, _, _) as x) u = contains_aux x off u ;;

let implode l =  
  let buf = BatUTF8.Buf.create ((List.length l) * 5) in
  List.iter (fun c -> BatUTF8.Buf.add_char buf c) l;
  of_ustring (BatUTF8.Buf.contents buf) ;;

let explode s =
  let l = ref [] in
  iter (fun x -> l := x :: !l) s;
  List.rev !l
;;


let enum s = explode s |> List.enum ;;

let escaped_aux ((_, bstart, bend, _) as s) = 
  let buffer = BatUTF8.Buf.create (BatUTF8.ByteIndex.to_int bend - BatUTF8.ByteIndex.to_int bstart) in
  s |> iter (fun u -> let ucode = UChar.code u in
		      if (ucode < 32) || (BatUTF8.contains "\"\\" u) then
			u |> BatUTF8.of_char |> BatUTF8.escaped |> BatUTF8.Buf.add_string buffer
                      else
			u |> BatUTF8.Buf.add_char buffer);
  BatUTF8.Buf.contents buffer ;;

let escaped s = escaped_aux s |> of_ustring ;;

let quote ((_, bstart, bend, _) as s) =
  let buf = BatUTF8.Buf.create (BatUTF8.ByteIndex.to_int bend - BatUTF8.ByteIndex.to_int bstart) in
  BatUTF8.Buf.add_string buf "\"";
  BatUTF8.Buf.add_string buf (escaped_aux s);
  BatUTF8.Buf.add_string buf "\"";
  BatUTF8.Buf.contents buf |> of_ustring
;;


let calculate_grow_size available needed old_len =
  
  let howmuch = ref 0 in
  let new_len = ref old_len in
  while needed > !howmuch + available do howmuch := !howmuch + !new_len ; new_len := 2 * !new_len done ;
  if !new_len > Sys.max_string_length then begin
    if !howmuch + old_len <= Sys.max_string_length
    then howmuch := Sys.max_string_length - old_len
    else failwith "UString.grow: cannot grow buffer"
  end ;
  !howmuch

;;


type bidx = int ;;

let grow_start ((s, bstart, bend, algn) as x) needed = 

  let old_len = String.length (BatUTF8.to_string_unsafe s) in
  let howmuch = calculate_grow_size (BatUTF8.ByteIndex.to_int bstart) needed old_len in
  let bstart' = BatUTF8.ByteIndex.to_int bstart in
  let bend'   = BatUTF8.ByteIndex.to_int bend in
  if howmuch > 0 then begin
    let new_s = String.create (String.length (BatUTF8.to_string_unsafe s) + howmuch) in
    let s' = BatUTF8.to_string_unsafe s in
    String.blit s' bstart' new_s (bstart'+howmuch) (bend' - bstart') ;
    (BatUTF8.of_string_unsafe new_s,
     BatUTF8.ByteIndex.of_int_unsafe (bstart'+howmuch), BatUTF8.ByteIndex.of_int_unsafe (bend'+howmuch),
     algn)
  end else x ;;

let grow_end  ((s, bstart, bend, algn) as x) needed =
  
  let old_len = String.length (BatUTF8.to_string_unsafe s) in
  let howmuch = calculate_grow_size (old_len - BatUTF8.ByteIndex.to_int bend) needed old_len in
  let bstart' = BatUTF8.ByteIndex.to_int bstart in
  let bend'   = BatUTF8.ByteIndex.to_int bend in
  if howmuch > 0 then begin
    let new_s = String.create (String.length (BatUTF8.to_string_unsafe s) + howmuch) in
    let s' = BatUTF8.to_string_unsafe s in
    String.blit s' bstart' new_s bstart' (bend' - bstart') ;
    (BatUTF8.of_string_unsafe new_s, bstart, bend, algn)
  end else x ;;

let append_bytes s bytes =
  
  let n = String.length bytes in
  let s' = grow_end s n in
  let (x, bstart, bend, _) = s' in
  let x' = BatUTF8.to_string_unsafe x in
  let bend' = BatUTF8.ByteIndex.to_int bend in
  String.blit bytes 0 x' bend' n ;
  (BatUTF8.of_string_unsafe x', bstart, BatUTF8.ByteIndex.of_int_unsafe (bend' + n), false)

;;


let prepend_bytes s bytes =

  let n = String.length bytes in
  let s' = grow_start s n in
  let (x, bstart, bend, _) = s' in
  let x' = BatUTF8.to_string_unsafe x in
  let bstart' = BatUTF8.ByteIndex.to_int bstart in
  String.blit bytes 0 x' (bstart' - n) n ;
  (BatUTF8.of_string_unsafe x', BatUTF8.ByteIndex.of_int_unsafe (bstart' - n), bend, false)

;;  

let append_uchar ((_,_,_,algn) as s) u =
  if not algn then failwith "appending to unaligned ustring"
  else
    (let (x,bstart,bend,_) = append_bytes s (BatUTF8.to_string_unsafe (BatUTF8.of_char u)) in
     (x,bstart,bend,true))
;;

let prepend_uchar ((_,_,_,algn) as s) u =
  if not algn then failwith "prepending to unaligned ustring"
  else
    (let (x,bstart,bend,_) = prepend_bytes s (BatUTF8.to_string_unsafe (BatUTF8.of_char u)) in
     (x,bstart,bend,true))
;;


let mkempty bstart bend =
  BatUTF8.of_string_unsafe (String.create (bstart+bend)),
  BatUTF8.ByteIndex.of_int_unsafe bstart,
  BatUTF8.ByteIndex.of_int_unsafe bstart,
  true
;;
  
(* module Camo = CamomileLibrary.UCharInfo.Make(CamomileLibrary.DefaultConfig) ;; *)
type general_category_type = Uucp.Gc.t;;

let category u = Uucp.Gc.general_category (Obj.magic u) ;;
let is_whitespace u = try Char.is_whitespace(UChar.char_of u) with _ -> false ;;
let is_uppercase u = try Char.is_uppercase(UChar.char_of u) with _ -> false ;;

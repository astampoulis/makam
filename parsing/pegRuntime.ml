open Utils;;
open Batteries;;

module Memotable =
  struct
    module M = 
	  Hashtbl.Make(struct
	    type t = int
	    let equal = (==)
	    let hash = Hashtbl.hash
	  end) ;;
	  
    type 'a t = ('a M.t) M.t * int ;;
    type 'a memocell =   MCLeft  of 'a M.t
		       | MCRight of ('a M.t) Lazy.t ;;
    let create n m = (M.create n, m) ;;

    let get_memocell (type a) (table, newsize) id : (a memocell) ref =
      match M.find_option table id with
	Some cell -> ref (MCLeft cell)
      | None      -> ref (MCRight (lazy(let newTbl = M.create newsize in
					let _      = M.add table id newTbl in
					newTbl)))
    ;;

    let find_in_memocell memocell offset =
      let open Option.Monad in
      bind (match !memocell with MCLeft x -> Some x | MCRight _ -> None) (fun existingIdTbl ->
      bind (M.find_option existingIdTbl offset) (fun existingOffsetEntry ->
	 return existingOffsetEntry))
    ;;

    let add_in_memocell memocell offset what =
      match !memocell with
	MCLeft memocell -> (M.remove_all memocell offset;
  			    M.add memocell offset what)
      | MCRight alloc   -> (let actualcell = Lazy.force alloc in
			    memocell := MCLeft actualcell ;
			    M.add actualcell offset what)
    ;;

  end ;;

let memotable_default () = Memotable.create 100 1000 ;;


module LRHash = Hashtbl.Make(struct
  type t  = int * int
  let equal (a1,a2) (b1,b2) = (a1 == b1) && (a2 == b2)
  let hash = Hashtbl.hash
end);;

type lrinfo = (bool ref * (Obj.t * UChannel.t) option ref) LRHash.t;;


let lrinfo_default () : lrinfo = LRHash.create 1000 ;;

let castLR (type a) (res : (Obj.t * UChannel.t) option) : (a * UChannel.t) option =
  match res with Some(x,y) -> Some (Obj.obj x, y) | None -> None
;;

let hideLR (type a) (res : (a * UChannel.t) option) : (Obj.t * UChannel.t) option =
  match res with Some(x,y) -> Some (Obj.repr x, y) | None -> None
;;

let compareLR (type a) (type b) (res1 : (a * UChannel.t) option) (res2 : (b * UChannel.t) option) : int =
  match res1, res2 with
    Some _, None -> 1
  | None, Some _ -> -1
  | None, None   -> 0
  | Some (_, input1), Some (_, input2) -> Stdlib.compare (UChannel.offset input1) (UChannel.offset input2)
;;
    

let growLR (type a) (used : bool ref) (resprev : (Obj.t * UChannel.t) option ref)
                    (func : unit -> (a * UChannel.t) option) : (a * UChannel.t) option =
  let rec aux () =
    let rescur = func () in
    if !used then
      (if compareLR rescur !resprev > 0 then
	  (resprev   := hideLR rescur;
	   aux ())
       else
	  castLR !resprev)
    else
      rescur
  in
  aux ()
;;
  


module Dict = Map.Make(String)
module StringSet = Set.Make(String)
module IMap = Map.Make(struct
			 type t = int
		         let compare = Pervasives.compare
		       end)
module StdHashtbl = Hashtbl
module DictHash = StdHashtbl.Make(struct
  type t = string ;;
  let equal s1 s2 = s1 = s2 ;;
  let hash = Hashtbl.hash ;;
end) ;;
module ConstStringHash = StdHashtbl.Make(struct
  type t = string ;;
  let equal s1 s2 = s1 == s2 ;;
  let hash = Hashtbl.hash ;;
end) ;;

(* make printf go through print_string, so as to work for js_of_ocaml *)
module Printf = struct
  include BatPrintf;;
  let printf fmt =
    ksprintf2 (fun s -> print_string s; flush stdout) fmt
  ;;
end;;


let (++) = List.append
let (||>) o1 o2 =
  match o1 with
      None -> Lazy.force o2
    | Some _ -> o1


let option_bool b x = match b with true -> Some x | false -> None ;;
let unescape s = Scanf.sscanf ("\"" ^ s ^ "\"") "%S%!" (fun u -> u) ;;

module ExtIMap = 
  struct
    exception AlreadyExists of int
    let addnew i what dict =
      if IMap.mem i dict then
	raise (AlreadyExists(i))
      else
	IMap.add i what dict
  end

module ExtDict =
  struct

    exception Not_found_key of string
    let find (a : string) b =
      try
	Dict.find a b
      with Not_found ->
	raise (Not_found_key(a))

    let getfst s dict =
      let (fst,snd) = find s dict in
	fst
	  
    let getsnd s dict = 
      let (fst,snd) = find s dict in
	snd

    exception AlreadyExists of string
    let addnew name what dict =
      if Dict.mem name dict then
	raise (AlreadyExists(name))
      else
	Dict.add name what dict

    let merge dexist d =
      Dict.fold
	(fun key v cur ->
	  if Dict.mem key cur then
	    cur
	  else 
	    Dict.add key v cur)
	d
	dexist


  end

type 'a dict = 'a Dict.t
type 'a map  = 'a IMap.t

let decreasing n = 
  let rec aux n = if n = 0 then [] else (n-1) :: aux (n-1) in
    aux n
let decreasing_start n start = 
  let rec aux n = if n = 0 then [] else (n-1+start) :: aux (n-1) in
    aux n
let increasing n = List.rev (decreasing n)

let uncurry f (a,b) = f a b

let option_ret  a = Some a
let option_bind e f = (match e with
			   Some e' -> f e'
			 | None -> None)
let option_monad = ( option_ret, option_bind )
let option_do f e = (match e with Some e -> Some (f e) | None -> None)
let option_or e1 e2 = match e1 with None -> e2 | Some _ -> e1

let (^?) s1 s2 = match s1 with Some(s) -> Some(s ^ s2) | None -> None

let compose f g x = f (g x)
let rec composemany fl x = match fl with [] -> x | hd :: tl -> hd (composemany tl x)
let id x = x

let require e why = (if not e then failwith why else ())

module ExtList =
  struct

    let findindex (f : 'a -> bool) (l : 'a list) =
      let rec aux i = function
	  [] -> raise Not_found
	| hd :: tl -> if f hd then i else aux (i+1) tl
      in
	aux 0 l

    let findrindex (f : 'a -> bool) (l : 'a list) =
      let rec aux i = function
	  [] -> raise Not_found
	| hd :: tl -> if f hd then i else aux (i-1) tl
      in
	aux (List.length l - 1) (List.rev l)

    let iteri (f : int -> 'a -> unit) (l : 'a list) =
      let rec aux i = function
	  [] -> ()
	| hd :: tl -> (f i hd; aux (i+1) tl)
      in
	aux 0 l

    let mapi (f : int -> 'a -> 'b) (l : 'a list) =
      let rec aux i = function
	  [] -> []
	| hd :: tl -> (f i hd) :: (aux (i+1) tl)
      in
	aux 0 l

    let insert (i : int) (t : 'a) (l : 'a list) =
      let rec aux i l =
	if i = 0 then t :: l
	else (match l with
	        hd :: tl -> hd :: (aux (i-1) tl) | _ -> failwith "ExtList.insert")
      in
      aux i l

    let remove (i : int) (l : 'a list) =
      let rec aux i l =
	match l with
	    hd :: tl -> if i = 0 then tl else hd :: (aux (i-1) tl)
	  | [] -> failwith "ExtList.remove"
      in
      aux i l

    let updatenth (n : int) (what : 'a) (l : 'a list) =
      mapi (fun i elm -> if i = n then what else elm) l

    let filtermapi (f : int -> 'a -> 'b option) (l : 'a list) =
      let rec aux i = function
	  [] -> []
	| hd :: tl -> 
	    let rest = aux (i+1) tl in
	      (match f i hd with
		   Some b -> b :: rest
		 | None -> rest)
      in
	aux 0 l

    let rec sublist (n : int) (l : 'a list) =
      if n = 0 then l else
	(match l with
	     [] -> failwith "ExtList.sublist"
	   | hd :: tl -> sublist (n-1) tl)

    (* let foldindex (f : int -> 'a -> 'b -> 'b) (start : 'b) (l : 'a list) = *)
    (*   let rec aux i = function *)
    (* 	  [] -> start *)
    (* 	| hd :: tl -> *)
    (* 	    f i hd (aux (i+1) tl) *)
    (*   in *)
    (* 	aux 0 l *)

    let foldindex (f : int -> 'a -> 'b -> 'b) (start : 'b) (l : 'a list) =
      let rec aux i res = function
    	  [] -> res
    	| hd :: tl ->
	    let res' = f i hd res in
	      aux (i+1) res' tl
      in
    	aux 0 start l

    exception LastOnEmpty
    let last (l : 'a list) =
      let rec aux res l = 
	match l with
	    t1 :: [] -> res, t1
	  | hd :: tl -> aux (hd :: res) tl
	  | _ -> raise LastOnEmpty
      in
      let rest, last1 = aux [] l in
	List.rev rest, last1
	  
    let last_two (l : 'a list) =
      let rec aux res l = 
	match l with
	    t1 :: t2 :: [] -> res, t1, t2
	  | hd :: tl -> aux (hd :: res) tl
	  | _ -> failwith "ExtList.last_two"
      in
      let rest, last1, last2 = aux [] l in
	List.rev rest, last1, last2

    let fstmap (f : 'a -> 'b) (l : ('a * 'c) list) =
      List.map (fun (a,c) -> (f a,c)) l

    let sndmap (f : 'a -> 'b) (l : ('c * 'a) list) =
      List.map (fun (c,a) -> (c,f a)) l

    let rec make (n : int) (elm : 'a) =
      if n = 0 then [] else elm :: make (n-1) elm

    let rec take (n : int) (l : 'a list) =
      if n = 0 then [] else match l with hd :: tl -> hd :: take (n-1) tl | [] -> failwith "take"

    let rec drop (n : int) (l : 'a list) =
      if n = 0 then l else match l with _ :: tl -> drop (n-1) tl | [] -> failwith "drop"

    let is_prefix l1 l2 =
      if List.length l1 > List.length l2 then false
      else List.for_all2 (=) l1 (take (List.length l1) l2)

    exception NotFoundPartition
    let find_partition_index f l =
      let rec aux index prev l =
	match l with
	    hd :: tl -> 
	      (if (f hd) then (List.rev prev, hd, tl), index
	       else aux (index+1) (hd :: prev) tl)
	  | [] ->
	      raise NotFoundPartition
      in
	aux 0 [] l

    let midfold f l res =
      let rec aux sofar l res =
	match l with
	    [] -> res
	  | hd :: tl -> let res' = f sofar hd res in
	                aux (List.append sofar [hd]) tl res'
      in
	aux [] l res

    let foldnonempty f empty one l =
      match l with
	[] -> empty
      | [hd] -> one hd
      | hd::tl -> List.fold_left f (one hd) tl

    let min_for_all2 f l1 l2 =
      let n1 = List.length l1 in
      let n2 = List.length l2 in
	if n1 > n2 then List.for_all2 f (take n2 l1) l2
	else List.for_all2 f l1 (take n1 l2)

    let split_at n l =
      let rec aux index prev l =
	match l with
	    hd :: tl -> 
	      (if index == n then (List.rev prev, hd, tl)
	       else aux (index+1) (hd :: prev) tl)
	  | [] ->
	    raise (Invalid_argument "Index past end of list")
      in
      aux 0 [] l

    let split4 l = 
      let (r1,r2,r3,r4) =
	List.fold_left
	  (fun (x,y,z,w) (a,b,c,d) -> a::x, b::y, c::z, d::w)
	  ( [], [], [], [] )
	  l
      in
      (List.rev r1, List.rev r2, List.rev r3, List.rev r4)
    ;;

    let rec option_map (f : 'a -> 'b option) (l : 'a list) : 'b list option =
      let rec aux acc l =
	match l with
	    [] -> Some (List.rev acc)
	  | hd :: tl -> (match f hd with None -> None | Some hd' -> aux (hd' :: acc) tl)
      in
      aux [] l
    ;;


  end


let rec repeatmany n (f : unit -> 'a) = if n = 1 then f () else (let _ = f () in repeatmany (n-1) f);;


let time_eval e =
  let start_time = Sys.time () in
  let _ = Lazy.force e in
  let end_time = Sys.time () in
  end_time -. start_time

let lexicographic_compare compareA compareB (a1, b1) (a2, b2) =
  let a_res = compareA a1 a2 in
  if a_res == 0 then compareB b1 b2 else a_res

let exn_to_option e =
  try
    Some(Lazy.force e)
  with _ -> None

let uncurry3 f (a,b,c) = f a b c ;;

module Pair = struct
  let map f (x,y) = f x, f y ;;
  let print ?(first="(") ?(last=")") ?(sep=",") f g oc (x,y) = BatPrintf.fprintf oc "%s%a%s%a%s" first f x sep g y last
end;;


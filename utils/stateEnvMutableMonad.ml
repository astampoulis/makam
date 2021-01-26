(* Monad for mutability with backtracking. Extends StateEnvMonad. *)
open Batteries;;
open Utils;;

type backtrack   = { btid      : int ;
		     btparent  : backtrack option ;
		     btmaxid   : int ref ;
		     btcheckpointed : bool ref ;
		     btundo    : (unit -> unit) list ref ;
		     btredo    : (unit -> unit) list ref }

let rootbt () = { btid = 0 ; btparent = None ; btmaxid = ref 0 ;
		  btcheckpointed = ref false ; btundo = ref [] ; btredo = ref [] } ;;
let newbt  parent : backtrack =
  parent.btmaxid := !(parent.btmaxid) + 1 ;
  { btid = !(parent.btmaxid) ; btparent = Some parent ; btmaxid = parent.btmaxid ;
    btcheckpointed = ref false ; btundo = ref [] ; btredo = ref [] } ;;
let btdo bt redo undo =
  redo () ;
  bt.btundo := undo :: !(bt.btundo) ;
  bt.btredo := redo :: !(bt.btredo)
;;

let btundo bt =
  !(bt.btundo) |> List.iter (fun f -> f ())
;;

let btredo bt =
  !(bt.btredo) |> List.rev |> List.iter (fun f -> f ())
;;

let btparents bt =
  let rec aux acc bt =
    match bt.btparent with
      None -> bt :: acc
    | Some parent -> aux (bt :: acc) parent
  in
  aux [] bt
;;

let btwarp bt bt' =
  let parents  = btparents bt  in
  let parents' = btparents bt' in
  let rec trimsame l l' =
    match l, l' with
      hd1 :: tl1, hd2 :: tl2 when hd1.btid == hd2.btid -> trimsame tl1 tl2
    | _ -> l, l'
  in
  let undo, redo = trimsame parents parents' in
  undo |> List.rev |> List.iter btundo ;
  redo |> List.iter btredo
;;


module Make = 
  functor (E : sig
    type env ;;
    type state ;;
    val  getbt : state -> backtrack ;;
    val  setbt : state -> backtrack -> state ;;
  end) ->
    struct

      include StateEnvMonad.Make(E) ;;

      let btdo redo undo =
	  let* state = getstate in
	  let bt  = E.getbt state in
	  let bt', updatecode =
	    if !(bt.btcheckpointed) then
	      begin
		bt.btcheckpointed := false ;
		let bt' = newbt bt in
		let state' = E.setbt state bt' in
		bt', setstate state'
	      end
	    else
	      bt, return ()
	  in
	  let _   = btdo bt' redo undo in
	  let* _ = updatecode in
	  return ()
      ;;

      let getbacktrackstate =
	  let* state = getstate in
	  let bt = E.getbt state in
	  let _  = bt.btcheckpointed := true in
	  return state
      ;;

      let setstate state' =
	  let* state = getstate in
	  let bt  = E.getbt state in
	  let bt' = E.getbt state' in
	  let _   = if bt.btid != bt'.btid then Benchmark.cumulative "backtrack warping" (lazy(btwarp bt bt')) else () in
	  setstate state'
      ;;


      module Ref =
      struct
	include Ref ;;
	let setM (type elm) (r : elm t) (w : elm) : unit m =
	    let* x = return 42 in
	    let p = !r in
	    btdo (fun () -> r := w) (fun () -> r := p)
	;;
      end;;

      module DynArray =
      struct
	include DynArray ;;
	let xtend (type elm) (a : elm t) (idx : int) (what : elm) : unit =
	  if DynArray.length a == idx then DynArray.add a what
	  else if idx < DynArray.length a then ()
	  else assert false
	;;
	let set (type elm) (idx : int) (what : elm) (a : elm t) : unit =
	  if DynArray.length a == idx then DynArray.add a what
	  else if idx < DynArray.length a then DynArray.set a idx what
	  else assert false
	;;
	let setM (type elm) (idx : int) (what : elm) (a : elm t) : unit m = 
	    let* x = return 42 in
            let* _ = (if DynArray.length a == idx then
		  (DynArray.add a what;
		   btdo (fun () -> DynArray.set a idx what) (fun () -> ()))
		else if idx < DynArray.length a then
		  (let p = DynArray.get a idx in
		   btdo (fun () -> DynArray.set a idx what)
		        (fun () -> DynArray.set a idx p))
		else
		  (assert false)) in
	    return ()
	;;
	let modifyM (type elm) (idx : int) (f : elm -> elm) (a : elm t) : unit m =
	    let* x = return 42 in
	    let* _ = (let p = DynArray.get a idx in
	      let p' = f p in
	      btdo (fun () -> DynArray.set a idx p')
		   (fun () -> DynArray.set a idx p))  in
	    return ()
	;;
	let find (type elm) (idx : int) (a : elm t) : elm =
	  try DynArray.get a idx with _ -> raise Not_found
	;;
      end;;

      module DictHash =
      struct
	include DictHash ;;
	
	let addM (type elm) (key : string) (v : elm) (a : elm t) : unit m =
	    let* x = return 42 in
            let* _ = (let res = try Some(DictHash.find a key) with _ -> None in
	      match res with
		Some p -> btdo (fun () -> DictHash.replace a key v)
		               (fun () -> DictHash.replace a key p)
	      | None   -> btdo (fun () -> DictHash.add a key v)
	                       (fun () -> DictHash.remove a key))  in
	    return ()
	;;
	
	let modify_defM (type elm) (default : elm) (key : string) (f : elm -> elm) (a : elm t) : unit m =
	    let* x = return 42 in
            let* _ = (let prev = try DictHash.find a key with _ -> (DictHash.add a key default; default) in
	      let cur  = f prev in
	      btdo (fun () -> DictHash.replace a key cur)
	           (fun () -> DictHash.replace a key prev))  in
	    return ()
	;;

	let find (type elm) (key : string) (a : elm t) : elm =
	  DictHash.find a key
	;;
      end
      ;;


    end;;


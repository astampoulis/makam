open Utils;;

let cumulative_times : float ConstStringHash.t = ConstStringHash.create 50 ;;
let loglist : (float * string * string * int) list ref = ref [] ;;
let enabled : bool ref = ref false ;;
(* let pausetimes : (float * float) list ref = ref [] ;; *)
let pausedtimeelapsed = ref 0.0 ;;

let time =
  let clock = match Oclock.process_cputime with Some x -> x | _ -> assert false in
  fun () -> (Int64.to_float (Oclock.gettime clock)) *. 1e-9 -. !pausedtimeelapsed
;;
  
let starttime () = time () ;;

let difftime start = 
  let endt = time () in
  (*
  let rec addpaused acc l =
    match l with
      (pausestart, pausedur) :: tl when pausestart > start -> addpaused (acc +. pausedur) tl
    | _ -> acc
  in
  *)
  endt -. start
;;

let return e =
  match e with
      `Left(e) -> e
    | `Right(x) -> raise x
;;

let timeforce e =
  let start = starttime () in
  let res   = try `Left(Lazy.force e) with e -> `Right(e) in
  let difft  = difftime start in
  ( difft, res )
;;

let forcepaused e =
  let (difft, res) = timeforce (lazy(Gc.minor (); Lazy.force e)) in
  (* let (difft, res) = timeforce e in *)
  pausedtimeelapsed := !pausedtimeelapsed +. difft ;
  (* pausetimes := (start, difft) :: !pausetimes ; *)
  res
;;

let force e =
  let (_, res) = timeforce e in
  res
;;

let cumulative_add s time =
  if !enabled then
	try 
	  let time' = ConstStringHash.find cumulative_times s in
	  ConstStringHash.replace cumulative_times s (time +. time')
	with Not_found ->
	  ConstStringHash.add cumulative_times s time
;;

let cumulative s e =
  let time, res = timeforce e in
  cumulative_add s time ;
  return res
;;
  
let cumulative_results () =
  let results = ConstStringHash.fold (fun fn_name fn_time cur -> (fn_name, fn_time) :: cur) cumulative_times [] in
  let sorted = List.sort (fun (x1,y1) (x2,y2) -> -(Pervasives.compare y1 y2)) results in
  sorted
;;

let log hd = loglist := hd :: !loglist ;;

let print_log oc =
  if List.length !loglist = 0 then () else
  let fulllog = List.rev !loglist in
  let starttime, _, _, _ = List.hd fulllog in
  let fulllog = List.map (fun (time, name, status, depth) -> time -. starttime, name, status, depth) fulllog in
  List.iter
    (fun (time, name, status, depth) ->
      BatPrintf.fprintf oc "%f,%s,%s%s\n" time status (BatString.repeat "·" depth) name) fulllog
;;

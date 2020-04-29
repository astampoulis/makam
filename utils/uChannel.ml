open Batteries ;;
open UChar;;

type loc      = { description : string ; lineno : int ; charno : int ; offset : int } ;;
type realspan = { startloc : loc ; endloc : loc } ;;
type span     = realspan option ;;


let string_of_loc loc  = Printf.sprintf "%s:%d:%d%!" loc.description loc.lineno loc.charno ;;
let string_of_span span : string =
  match span with
      None -> "<none>"
    | Some({startloc = locstart ; endloc = locend }) ->
      begin
        assert(locstart.description = locend.description);
        if locstart.lineno = locend.lineno then begin
          if locstart.charno = locend.charno then
            string_of_loc locstart
          else
            Printf.sprintf "%s:%d:%d-%d%!" locstart.description locstart.lineno locstart.charno locend.charno
          end
        else
          Printf.sprintf "%s:%d.%d-%d.%d%!" locstart.description locstart.lineno locstart.charno locend.lineno locend.charno
      end
;;

let loc_compare loc1 loc2 =
  if loc1.description <> loc2.description then assert false
  else
    Pervasives.compare loc1.offset loc2.offset
    (*
    (let res = Pervasives.compare loc1.lineno loc2.lineno in
     if res = 0 then Pervasives.compare loc1.charno loc2.charno else res)
    *)
;;

let span_end span =
  Utils.option_do (fun { endloc = l } -> { startloc = l ; endloc = l }) span
;;

let mk_span startloc endloc =
  try
    if loc_compare startloc endloc <= 0 then
      Some { startloc = startloc ; endloc = endloc }
    else
      None
  with _ -> None
;;

let combine_span span1 span2 =
  match span1, span2 with
    Some { startloc = startloc }, Some { endloc = endloc } -> mk_span startloc endloc
  | Some _, None -> span1
  | None, Some _ -> span2
  | _ -> None
;;


(* Channel implementation starts *)


type t = { contents : UString.t ref ; location : loc ;
           current  : UString.bidx ;
           furthest : UString.bidx ref ; furthest_loc : loc ref ;
           reached_eof : bool ref ;
           looknext : UString.bidx -> UChar.t * UString.bidx ;
           update_statehash : bool } ;;

let from_string  ?(initloc={ description = "<string>" ; lineno = 1; charno = 1; offset = 0 }) string =
  let str = ref (UString.of_string string) in
  { contents = str ; current = 0 ;
    furthest = ref 0 ; furthest_loc = ref initloc ;
    reached_eof = ref true ;
    location = initloc ;
    update_statehash = false ;
    looknext = (fun off ->
      if UString.is_end !str off then raise IO.No_more_input
      else UString.looknext_unsafe !str off) } ;;

let from_filename ?(statehash_update = true) filename =
  let input = File.open_in filename in
  let str   = IO.read_all input in
  let _     = IO.close_in input in
  let location = { description = "file " ^ filename ; lineno = 1 ; charno = 1; offset = 0 } in
  { from_string ~initloc:location str with update_statehash = statehash_update }
;;

let from_filename_buffered ?(buffersize = 1024) filename =
  let input = File.open_in filename in
  let str   = ref (UString.mkempty 0 (buffersize*2)) in
  let reached_eof = ref false in
  let initloc = { description = "file " ^ filename ; lineno = 1 ; charno = 1; offset = 0 } in
  { contents = str ; current = 0 ;
    furthest = ref 0 ; furthest_loc = ref initloc ;
    reached_eof = reached_eof ;
    location = initloc;
    update_statehash = true ;
    looknext = (fun off ->
      if UString.safe_offset !str off then UString.looknext_unsafe !str off
      else if !reached_eof then raise IO.No_more_input
      else
        (try
           let newbytes = IO.nread input buffersize in
           str := UString.append_bytes !str newbytes ;
           if UString.safe_offset !str off then UString.looknext_unsafe !str off
           else raise (Invalid_argument ("UChannel.from_filename_buffered: invalid UTF8 encoding in " ^ filename))
         with IO.No_more_input -> (reached_eof := true ; IO.close_in input ; raise IO.No_more_input)))
  }
;;


let from_stream ?(initloc={ description = "<stream>" ; lineno = 1; charno = 1; offset = 0}) s =
  let str   = ref (UString.mkempty 0 1024) in
  let reached_eof = ref false in
  { contents = str ; current = 0 ;
    furthest = ref 0 ; furthest_loc = ref initloc;
    reached_eof = reached_eof ;
    location = initloc ;
    update_statehash = true ;
    looknext = (fun off ->
      if not (UString.is_end !str off) then UString.looknext_unsafe !str off
      else if !reached_eof then raise IO.No_more_input
      else
        (try
           let u = Text.read_char s in
           str := UString.append_uchar !str u ;
           UString.looknext_unsafe !str off
         with IO.No_more_input -> (reached_eof := true ; raise IO.No_more_input))) }
;;

let from_stdin () =
  let initloc =
    if Unix.isatty Unix.stdin then
      { description = "<repl>" ; lineno = 1; charno = 1; offset = 0}
    else
      { description = "<stdin>" ; lineno = 1; charno = 1; offset = 0}
  in
  from_stream ~initloc:initloc IO.stdin
;;

let offset c = c.location.offset ;;
let loc    c = c.location ;;
let reached_eof c = !(c.reached_eof) ;;
let at_eof c = UString.is_end !(c.contents) c.current && !(c.reached_eof) ;;

let input_statehash = ref 0;;

let get_one c =
  try
    let u, next = c.looknext c.current in
    let ucode = UChar.code u in
    let addline = ucode == 10 || ucode == 13 in
    let loc = c.location in
    let newloc =
      if addline
      then { loc with lineno = loc.lineno + 1 ; charno = 1; offset = loc.offset + 1 }
      else { loc with charno = loc.charno + 1 ; offset = loc.offset + 1 }
    in
    let _ =
      if next > !(c.furthest) then (
        (if (c.update_statehash) then
          input_statehash := Hashtbl.hash (!input_statehash + ucode));
        c.furthest := next; c.furthest_loc := newloc
      )
    in
    Some (u, { c with current = next ; location = newloc})
  with IO.No_more_input -> None
;;

let map f c =
  let rec aux acc c =
    match get_one c with
      None -> List.rev acc
    | Some (hd, c') -> aux (f c hd :: acc) c'
  in
  aux [] c
;;

let flush_to_furthest uc =
  { uc with current = !(uc.furthest); location = !(uc.furthest_loc) }
;;

(*

  Extensible datatype definitions
  -------------------------------
  Written by Antonis Stampoulis; licensed under GPLv3.


  Usage:

   /Definition/

  xtype expr = 
    `Var    of name : string
  | `Lambda of name : string ; body : expr
  | `App    of func : expr ; arg : expr

  (Generate a new type, with the definition:
    data expr = 
        Var of < name : string >
     | ... )
  
   /Concrete value/

  <{ App func = <{ Lambda name = "x" ; body = <{ Var name = "x" }> }> ;
         expr = <{ Var name = "x" }> }>

   /Pattern matching and derived value/

  match e with
    `Var o -> <{ Var name = String.uppercase o#name ; .. = o }>

  The above would still work even if we extended the constructor of Var
  with further components; note that the definition of the function would
  have to be rewritten, as we are not using real variants right now.

   /Extension/
  xtype expr = 
    `Var of db : int
  | `any of loc : location

  Now the above derived value would desugar into:
   `Var { name = String.uppercase o#name ; db = o#db }

  Currently known bugs: 
   - can't handle mutually dependent non-concrete definitions
*)


open Camlp4

module Id = struct
  let name = "syntax_xtype"
  let version = "1.0"
end

(* utility functions *)
let (++) = List.append ;;
module Dict = Map.Make(String);;
module StringSet = Set.Make(String)
module ExtList =
  struct

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

    let rec drop (n : int) (l : 'a list) =
      if n = 0 then l else match l with _ :: tl -> drop (n-1) tl | [] -> failwith "drop"
  end;;

(* actual extension *)

module Make (Syntax : Sig.Camlp4Syntax) = struct
  open Sig
  include Syntax

  let xtypes_dict = ref Dict.empty;;
  let xtypes_new_entries = ref [] ;;


  let appmany _loc start what = List.fold_left (fun cur elm -> <:ctyp< $elm$ $cur$ >> ) start what ;;
  
  let xappmany start what = List.fold_left (fun cur elm -> `XApp(elm,cur)) start (List.rev what) ;;
    
  let r = ref 0 ;;

  let expand_xtype x poly _loc =
    let r = (r := !r + 1); !r in
    let (absnames, _) = Dict.find x !xtypes_dict in
    let absnames = ExtList.drop (List.length poly) absnames in
    let params = List.map (fun t -> 
      let t = "x" ^ (string_of_int r) ^ t in <:ctyp< '$lid:t$ >> ) absnames in
    let params = poly ++ params in
    appmany _loc <:ctyp< $lid:x$ >> params
  ;;

  let xtype_find_deps constrs =
    let d = ref StringSet.empty in
    let _ =
      List.iter
	(fun (_,fields) ->
	  List.iter
	    (fun (_,typ) ->
	      let rec aux typ =
		match typ with
		    `XConst(xname) when Dict.mem xname !xtypes_dict ->
		      d := StringSet.add xname !d
		  | `XConst(_) -> ()
		  | `XAsIs(_) -> ()
		  | `XRef(t) -> aux t
		  | `XApp(t1,t2) -> aux t1; aux t2
		  | `XPoly(_) -> ()
	      in
	      aux typ)
	    fields)
	constrs
    in
    StringSet.elements !d
  ;;

  let xtype_declare (name, poly, constrs, concrete) _loc =

    let xtypes = xtype_find_deps constrs in

    let ctypize id = <:ctyp< '$lid:id$ >> in

    let constrnames = List.map fst constrs in
    let xtypenames  =
      List.combine
	xtypes
	(List.map
	   (fun x -> 
	     let (absnames, _) = Dict.find x !xtypes_dict in
	     List.map ( (^) ("b" ^ x) ) absnames) xtypes)
    in

    let constrtypv  = List.map ( (^) "a" ) constrnames in
    let xtyptypv    = List.map ( (^) "b" ) (List.flatten (List.map snd xtypenames)) in
    let polytypv    = List.map ( (^) "p" ) poly in
    let maintypv    = "c" ^ name in
    let alltypv     = polytypv ++ (if concrete then xtyptypv else (maintypv :: xtyptypv ++ constrtypv))  in
    let params      = List.map ctypize alltypv in
    
    let rec map_type t = 
      match t with
	  `XConst(xname) when xname = name -> appmany _loc <:ctyp< $lid:xname$ >> params
	| `XConst(xname) when List.mem xname xtypes ->
	  let xparams = List.map ctypize (List.assoc xname xtypenames) in
	  appmany _loc <:ctyp< $lid:xname$ >> xparams
	| `XConst(name) -> <:ctyp< $lid:name$ >>
	| `XAsIs(ctyp) -> ctyp
	| `XRef(t) -> let t = map_type t in <:ctyp< ref $t$ >>
	| `XApp(arg,tc) -> appmany _loc (map_type tc) [map_type arg]
	| `XPoly(n) -> let n = "p" ^ n in <:ctyp< ' $lid:n$ >>
    in

    let map_fields paramv fs =
      let ml = List.map (fun (n,xt) ->
	let t = map_type xt in
	(* <:ctyp< $lid:n$ : $t$ >> *)
	Ast.TyCol (_loc, Ast.TyId (_loc, Ast.IdLid (_loc, n)), t)) fs
      in
      List.fold_left (fun cur elm -> <:ctyp< $elm$ ; $cur$ >> ) <:ctyp< >> ml
    in

    let map_constr which (cname, fields) =
      let t = map_fields ( "a" ^ cname ) fields in
      if concrete then
	 <:ctyp< `$uid:cname$ of < $t$ > >>
      else
	<:ctyp< `$uid:cname$ of ( < $t$ ; .. > as '$lid:which$ ) >>
    in

    let constrtypes = List.map2 map_constr constrtypv constrs in
    let maintyp = List.fold_left (fun cur elm -> <:ctyp< $cur$ | $elm$ >> ) <:ctyp< >> constrtypes in
    let mytyp = 
      if concrete then
	<:ctyp< ( [ $maintyp$ ] ) >>
      else
	<:ctyp< ( [> $maintyp$ ] as '$lid:maintypv$ ) >>
    in

    let decl = 
      Ast.TyDcl( _loc, name, params, mytyp, [] )
    in

    let _ =
      xtypes_dict :=
	Dict.add name
	( alltypv , 
	  (name, poly, constrs, concrete) )
	!xtypes_dict ;
      xtypes_new_entries := 
	!xtypes_new_entries ++
	if List.mem name !xtypes_new_entries then [] else [name] 
    in
    decl ;;
  
  let xtype_extend xname bname xpoly remaps xaddfields xconstrs _loc =

    let (_, (bname, bpoly, bconstrs, _) ) = Dict.find bname !xtypes_dict in

    let bconstrs =
      List.map (fun (cn, fields) -> (cn, fields ++ xaddfields)) bconstrs	
    in

    let btype_mapping = (bname,xname) :: remaps in
    let poly_mapping = List.combine bpoly xpoly in
    
    let map_field (name, typ) =
      let rec map_type typ =
	match typ with
	  `XConst(cname) ->
	    (try let newname = List.assoc cname btype_mapping in `XConst(newname)
	     with Not_found -> `XConst(cname))
	| `XAsIs(cname) -> `XAsIs(cname)	   
	| `XRef(t) -> `XRef(map_type t)
	| `XApp(arg,tc) -> `XApp(map_type arg, map_type tc)
	| `XPoly(cname) ->
	    (try List.assoc cname poly_mapping
	     with Not_found -> `XPoly(cname))
      in
      let typ' = map_type typ in
      (name, typ')
    in

    let map_constructor (name, fields) =
      let newfields =
	try List.assoc name xconstrs
	with Not_found -> []
      in
      (name, (List.map map_field fields) ++ newfields)
    in

    let old_constructors = List.map map_constructor bconstrs in
    let new_constructors = 
      ExtList.filtermapi
	(fun _ (name, fields) ->
	  try let _ = List.assoc name old_constructors in None
	  with Not_found -> Some (name, fields))
	xconstrs
    in

    old_constructors ++ new_constructors

  ;;


  let xtype_ctx rname rpoly ctxname bname xpoly remaps _loc =

    let (_, (bname, bpoly, bconstrs, _) ) = Dict.find bname !xtypes_dict in

    let poly_mapping = List.combine bpoly xpoly in
    
    let field_contains_ctx (_, typ) =
      let rec contains typ =
	match typ with
	  `XConst(cname) when cname = ctxname -> true
	| `XConst(cname) -> (try
			       let (_, (_, _, oconstrs, _) ) = Dict.find cname !xtypes_dict in
			       List.fold_left (fun b (_,c) -> b || List.exists (fun (_,t) -> contains t) c) false oconstrs
	                     with _ -> false)
	| `XAsIs(_) -> false
	| `XRef(t) -> if contains t then failwith "can't derive context type of reference type" else false
	| `XApp(t1,t2) -> if contains t1 || contains t2 then failwith "can't derive context type of type constructor applications yet" else false
	| `XPoly(_) -> false
      in
      contains typ
    in
        
    let map_field (name, typ) =
      let rec map_type typ =
	match typ with
	  `XConst(cname) ->
	    (try let newname = List.assoc cname remaps in `XConst(newname)
	     with Not_found -> `XConst(cname))
	| `XAsIs(cname) -> `XAsIs(cname)
	| `XRef(t) -> `XRef(map_type t)
	| `XApp(arg,tc) -> `XApp(map_type arg, map_type tc)
	| `XPoly(cname) ->
	    (try List.assoc cname poly_mapping
	     with Not_found -> `XPoly(cname))
      in
      let typ' = map_type typ in
      (name, typ')
    in

    let map_constructor (name, fields) =
      List.fold_left
	(fun curconstr ((fname,typ) as field) ->
	  if field_contains_ctx field then
	    let newfields = 
	      (List.map map_field (List.remove_assoc fname fields)) ++
	      [ "up", xappmany (`XConst(rname)) (List.map (fun s -> `XPoly s) rpoly) ]
	    in
	    curconstr ++ [ "Ctx"^name^(String.capitalize fname), newfields ]
	  else
	    curconstr)
	[] fields
    in

    let constructors = List.flatten (List.map map_constructor bconstrs) in
    let constructors = ( "CtxTop", [] ) :: constructors in

    constructors

  ;;


  let xtype_get_fields typname constrname _loc = 
    if typname = "" then failwith "can't use field extension when type is not specified";
    let (_, (_,_,constrs,_)) = Dict.find typname !xtypes_dict in
    List.assoc constrname constrs
  ;;

  let xinclude s _loc =
    let f = try open_in_bin (s ^ ".ml.xtypes") with _ -> open_in_bin ("_build/" ^ s ^ ".ml.xtypes") in
    let newentries = Marshal.from_channel f in
    xtypes_dict := List.fold_left (fun dict (n,v) -> Dict.add n v dict) !xtypes_dict newentries;
    close_in f ;;

  let xsave s _loc =
    let entries = List.map (fun n -> n, Dict.find n !xtypes_dict) !xtypes_new_entries in
    let f = open_out_bin (s ^ (".ml.xtypes")) in
    Marshal.to_channel f entries [];
    close_out f ;;
    


  EXTEND Gram
    GLOBAL: str_item sig_item ctyp expr;

    str_item: LEVEL "top"
      [ [ "xtype"; ts = LIST1 xtype_declaration SEP "and" ->
          let decls =
	    let ts = List.map (fun t -> xtype_declare t _loc) ts in
            match ts with
		hd :: tl -> List.fold_left
		  (fun cur elm -> <:ctyp< $cur$ and $elm$ >> ) hd tl
	      | _ -> failwith ""
	  in
          <:str_item< type $decls$ >>
	| "xinclude"; a = STRING -> xinclude a _loc; <:str_item< >>
        | "xsave"; a = STRING -> xsave a _loc; <:str_item< >>
        | "xopen"; a = UIDENT -> xinclude (String.uncapitalize a) _loc; <:str_item< open $uid:a$ >>
	] ] ;

    sig_item: LEVEL "top"
      [ [ "xtype"; ts = LIST1 xtype_declaration SEP "and" ->
          let decls =
	    let ts = List.map (fun t -> xtype_declare t _loc) ts in
            match ts with
		hd :: tl -> List.fold_left
		  (fun cur elm -> <:ctyp< $cur$ and $elm$ >> ) hd tl
	      | _ -> failwith ""
	  in
          <:sig_item< type $decls$ >>
	| "xinclude"; a = STRING -> xinclude a _loc; <:sig_item< >>
        | "xsave"; a = STRING -> xsave a _loc; <:sig_item< >>
        | "xopen"; a = UIDENT -> xinclude (String.uncapitalize a) _loc; <:sig_item< open $uid:a$ >>
	] ] ;

    xtype_declaration:
      [ [ poly = xtype_poly; name = LIDENT ->
          ( name, poly, [], true )

	| poly = xtype_poly; name = LIDENT; "="; cs = LIST1 xtype_constructors SEP "|" -> 
	  (name, poly, cs, true )

	| poly = xtype_poly; name = LIDENT; "=";
	  "extend"; xpoly = xtype_poly_inst_xt; xname = LIDENT; remaps = xtype_remaps; "with";
	  cs = xtype_update_constructors -> 
	  let (addtoall, csupd) = cs in
	  let cs' = xtype_extend name xname xpoly remaps addtoall csupd _loc in
	  (name, poly, cs', true)

	| poly = xtype_poly; name = LIDENT; "=";
	  "extend"; xpoly = xtype_poly_inst_xt; xname = LIDENT; remaps = xtype_remaps -> 

	  let cs' = xtype_extend name xname xpoly remaps [] [] _loc in
	  (name, poly, cs', true)

	| poly = xtype_poly; name = LIDENT; "=";
	  "context"; holename = LIDENT; "in"; xpoly = xtype_poly_inst_xt; xname = LIDENT; remaps = xtype_remaps ->
	  let cs = xtype_ctx name poly holename xname xpoly remaps _loc in
	  (name, poly, cs, true)
	  
	] ] ;

    xtype_poly:
      [ [ "'"; i = LIDENT; ts = xtype_poly -> i :: ts
	| -> [] ] ];

    xtype_poly_inst_xt:
      [ [ "'"; i = LIDENT; ts = xtype_poly_inst_xt -> `XPoly(i) :: ts
	| "("; t = xtypes; ")"; ts = xtype_poly_inst_xt -> t :: ts
	| -> [] ] ];      

    xtype_poly_inst:
      [ [ "'"; i = LIDENT; ts = xtype_poly_inst -> <:ctyp< ' $lid:i$ >> :: ts
	| "("; t = ctyp; ")"; ts = xtype_poly_inst -> t :: ts
	| -> [] ] ];

    xtype_remaps:
      [ [ -> []
	| "["; n = LIST1 [ x = LIDENT; "~>"; y = LIDENT -> x,y ] SEP ";"; "]" -> n ] ];

    xtype_update_constructors:
      [ [ cs = LIST1 xtype_constructors SEP "|" -> ( [], cs )
	| "`"; "any"; addtoall = LIST1 xtype_fields SEP ";" -> ( addtoall, [] )
	|  "`"; "any"; addtoall = LIST1 xtype_fields SEP ";"; "|";
	  cs = LIST1 xtype_constructors SEP "|" -> ( addtoall, cs ) ] ];

    xtype_constructors:
      [ [ "`"; name = UIDENT -> (name, [])
	| "`"; name = UIDENT; ts = LIST1 xtype_fields SEP ";" -> (name, ts) ] ] ;

    xtype_fields:
      [ [ name = LIDENT; ":"; t = xtypes -> (name,t) ] ] ;

    xtypes:
      [ [ name = LIDENT -> `XConst(name)
	| name = val_longident -> `XAsIs( <:ctyp< $id:name$ >> )
	| "{"; ct = poly_type; "}" -> `XAsIs(ct)
	| "tref"; arg = xtypes -> `XRef(arg)
	| arg = xtypes; tcons = xtypes -> `XApp(arg, tcons)
	| "'"; p = LIDENT -> `XPoly(p)
	| "("; x = xtypes; ")" -> x ] ] ;

    ctyp: LEVEL "simple"
      [ [ "<"; "{"; poly = xtype_poly_inst; name = LIDENT; "}"; ">" -> expand_xtype name poly _loc ] ];

    expr_field:
      [ [ name = LIDENT; "="; e = expr LEVEL "top" -> (name,e)
	| ".."; "="; e = expr LEVEL "top" -> ("_existing", e) ] ];

    update_fields:
      [ [ fields = LIST0 expr_field SEP ";" ->

	  fun tname cname ->

	    let oldfields_expr, fields =
	      try Some( List.assoc "_existing" fields ), List.remove_assoc "_existing" fields
	      with Not_found -> None, fields
	    in

	    let existing =
	      match oldfields_expr with
		  Some e ->
		    let oldfields = xtype_get_fields tname cname _loc in
		    let oldfields' = ExtList.filtermapi (fun _ (n,_) -> try let _ = List.assoc n fields in None with Not_found -> Some n) oldfields in
		    let existing = List.map (fun n -> (n, <:expr< $e$ # $lid:n$ >> ) ) oldfields' in
		    existing
		| None -> []
	    in
	    fields ++ existing ] ];

    expr: LEVEL "simple"
      [ [ "<"; "{"; tname = [ tname = LIDENT; "." -> tname | -> "" ]; cname = UIDENT; get_fields = update_fields; "}"; ">" -> 
          let fields = get_fields tname cname in
          let fval =
            List.map (fun (name, e) ->
	      let constname = "_const_" ^ name in
	      <:class_str_item< val $lid:constname$ = $e$ ;; method $lid:name$ = $lid:constname$ >> ) fields
	  in
	  let start = <:class_str_item< >> in
	  let combine cur elm = Ast.CrSem(_loc, elm, cur) in
	  let methods = List.fold_left combine start fval in
	  let obj = Ast.ExObj(_loc, Ast.PaNil(_loc), methods) in
	  <:expr< `$lid:cname$ $obj$ >>
	  (* <:expr< object $methods$ end >> *) 
	| "#"; "#"; i = label -> <:expr< fun x -> x # $i$ >> 
	| "#"; "!"; i = UIDENT -> <:expr< function (`$uid:i$ o) -> o | _ -> failwith "" >> ] ] ;

    expr: LEVEL "."
      [ [ e = SELF; "#"; "!"; i = UIDENT ->
          <:expr< match $e$ with (`$uid:i$ o) -> o | _ -> failwith "" >> ] ] ;

  END

end

module M = Register.OCamlSyntaxExtension(Id)(Make)


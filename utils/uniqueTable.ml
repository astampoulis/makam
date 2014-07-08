module Make =
  functor (HType : Hashtbl.HashedType) ->

    (* The Hashtable in the Batteries version currently included in GODI
       is buggy [uses (=) instead of HashedType.equal to compare equality],
       so we are using the normal Hashtable from OCaml's standard library here. *)

    struct
      
      type uobj = { obj : HType.t ; tag : int ; hcode : int }
      module EqHash = Hashtbl.Make(HType)
      type t = uobj EqHash.t * int ref

      let create n = EqHash.create n, ref 0

      let uobj (uobjmap,counter) v =
	try
	  EqHash.find uobjmap v
	with _ ->
	  (let newtag = !counter in
	   let uobj = { obj = v ; tag = newtag ; hcode = HType.hash v } in
	   counter := newtag + 1;
	   EqHash.add uobjmap v uobj;
	   uobj)
      ;;
	
      let uniqueTag uobjmap v = (uobj uobjmap v).tag

    end;;


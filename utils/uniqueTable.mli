module Make :
  functor (HType : Hashtbl.HashedType) ->
    sig
      
      type uobj = { obj : HType.t ; tag : int ; hcode : int }
      type t
      val create : int -> t
      val uobj : t -> HType.t -> uobj
      val uniqueTag : t -> HType.t -> int

    end;;

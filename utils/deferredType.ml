open Batteries ;; 

module type Type = 
  sig
    val uniquetag : int ;;
    type t ;;
    val empty : unit -> t
  end ;;

module Make = functor (T : Type) ->
  (struct
    let castin (type a) (x : a) : Obj.t = Obj.repr (x, T.uniquetag) ;;
    let castout (type a) (x : Obj.t ref) : a =
      let (r, u') = Obj.obj !x in
      if u' == 0 then
	(let r = T.empty () in
	 x := castin r ; Obj.magic r)
      else
	((* try assert (u' == T.uniquetag) with e -> BatPrint.printf p"oops %d instead of %d\n" u' T.uniquetag; raise e ;*)
	 r)
    ;;
    (* let empty () = ref (castin (T.empty())) ;; *)
    let empty = 
      let res = ref (castin (T.empty())) in
      fun () -> res
    ;;
   end)
;;

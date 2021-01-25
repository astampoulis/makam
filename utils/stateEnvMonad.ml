(* Monad with state and environment. *)

open Utils;;

type ('env, 'state) ctx = { env : 'env ; state : 'state } ;;

module Make =
  functor (E : sig
    type env ;;
    type state ;;
  end) ->
    struct
      type 'a m = (E.env, E.state) ctx -> 'a * E.state ;;
      let return (type a) (x : a) : a m = fun ctx -> x, ctx.state ;;
      let bind   (type a) (type b) (f : a m) (g : a -> b m) : b m =
	fun ctx ->
	let a, state' = f ctx in
	g a { ctx with state = state' } ;;
      let ( let* ) = bind ;;
      let lazyreturn (type a) (x : a Lazy.t) : a m =
	fun c -> Lazy.force x, c.state
      ;;
      exception CurCtx of exn * (E.env, E.state) ctx ;;
      let mraise (type a) (e : exn) : a m =
	fun c -> raise (CurCtx(e, c)) ;;
      let mtry   (type a) (a : a m) (f : exn -> a m) : a m =
	fun c -> try a c with CurCtx(e, c') -> f e c' ;;
      let mchoice (type a) ?(expectedException = fun _ -> true) (f : a m) (g : a m) : a m =
	mtry f (fun e -> if expectedException e then g else mraise e) ;;
      let getctx   : (E.env, E.state) ctx m = fun c -> c, c.state ;;
      let getenv   : E.env m = fun c -> c.env, c.state ;;
      let getstate : E.state m = fun c -> c.state, c.state ;;
      let setstate (state' : E.state) : unit m = fun ctx -> (), state' ;;
      let inenv      (type a) (env' : E.env) (f : a m) : a m = fun ctx -> f { ctx with env = env' }  ;;
      let choice    
	  (type a)
	  ?(expectedException = fun _ -> true)
	  (f : a m) (g : a m) : a m =
          fun ctx -> 
	  try f ctx with e when expectedException e -> g ctx | e -> raise e
      ;;
      let bindlist (type a) (l : (a m) list) : (a list) m =
	List.fold_left (fun mList mElm ->
	                  let* list = mList in
	                  let* elm  = mElm  in
		          return (list ++ [elm])) (return []) l ;;
      let mapM     (type a) (type b) (f : a -> b m) (l : a list) : (b list) m =
	bindlist (List.map f l) ;;
      let foldM    (type a) (type b) (f : a -> b -> a m) (s : a) (l : b list) : a m =
	List.fold_left (fun s e -> 
                        let* s' = s in
	                f s' e)
	  (return s) l ;;
      let foldmapM (type a) (type b) (type c)
	           (f : a -> b -> (a * c) m) (s : a) (l : b list) : (a * (c list)) m =
        let* (res, lrev) = foldM (fun (cur, lrev) elm ->
	                           let* (cur', elm') = f cur elm in
	                           return (cur', elm' :: lrev)) (s, []) l  in
	  return (res, List.rev lrev)
      ;;
      let benchM (type a) (s : string) (f : (a m) Lazy.t) : a m =
	fun c -> Benchmark.cumulative s (lazy((Lazy.force f) c))
      ;;

    end;;

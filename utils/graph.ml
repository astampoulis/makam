(* Graph library
   -------------

   For the time being, I've only implemented topological sorting;
   and a kind of topological sorting for cyclic graphs, where cycles are
   identified and coalesced before performing normal topological sorting.
   These are useful to identify mutual recursion blocks from a dependency
   graph.
*)

open Batteries;;
open Utils;;

module Make =

  functor (Node : sig
    include Interfaces.OrderedType
    val to_string : t -> string
  end) ->
  struct

    module Node = struct
      include Node
      let equal n1 n2 = compare n1 n2 == 0
    end;;
    module NodeSet = Set.Make(Node) ;;
    module NodeMap = Map.Make(Node) ;;

    type dgraph = { nodes : Node.t list ; edges : NodeSet.t NodeMap.t } ;;

    let printer_node oc x = Printf.fprintf oc "%s" (Node.to_string x) ;;
    let printer_nodeset oc x = Printf.fprintf oc "%a" (NodeSet.print ~first:"[" ~sep:"," ~last:"]" printer_node) x ;;
    let printer_nodelist oc x = Printf.fprintf oc "%a" (List.print ~first:"[" ~sep:"," ~last:"]" printer_node) x ;;

    let reverse (dg: dgraph) =
    
      let edges'Empty = dg.nodes |> List.map (fun n -> n, NodeSet.empty) |> List.enum |> NodeMap.of_enum in
      let edges' =
	NodeMap.fold
	  (fun node pointsto edges' ->
	    NodeSet.fold
	      (fun node' edges' -> NodeMap.modify node' (NodeSet.add node) edges')
	      pointsto
	      edges')
	  dg.edges
	  edges'Empty
      in
      { nodes = dg.nodes; edges = edges' }

    let topo_sort (dg: dgraph) =

      let processed = ref NodeSet.empty in
      let result = ref [] in
      let rec visit node = 

	if not (NodeSet.mem node !processed) then 
	  (processed := NodeSet.add node !processed;
	   NodeMap.find node dg.edges |> NodeSet.iter visit;
	   result := node :: !result)
	    
      in
      
      List.iter visit dg.nodes;
      !result


    let cyclic_topo_sort dg =

      let module NodeMap = 
	  struct 
	    include NodeMap
	    let from_list l = l |> List.enum |> NodeMap.of_enum
	    let replace (key : Node.t) (where : ('a ref) NodeMap.t) (newvalue : 'a) =
	      (NodeMap.find key where) := newvalue
	  end
      in

      let parents = dg.nodes |> List.map (fun n -> (n, ref n)) |> NodeMap.from_list in
      let children = dg.nodes |> List.map (fun n -> (n, ref (NodeSet.singleton n))) |> NodeMap.from_list in
      let combedges = dg.nodes |> List.map (fun n -> (n, ref (NodeMap.find n dg.edges))) |> NodeMap.from_list in
      let parentOf n = NodeMap.find n parents in
      let childrenOf n = NodeMap.find n children in
      let combedgesOf n = NodeMap.find n combedges in
      let edgesOf n = NodeMap.find n dg.edges in

      let printer_nodeinfo oc n =
	Printf.printf "Node %a:\n\tParent: %a\n\tChildren: %a\n\tCombedges: %a\n"
	  printer_node n
	  printer_node !(parentOf n)
	  printer_nodeset !(childrenOf n)
	  printer_nodeset !(combedgesOf n)
      in

      let find_cycles () =

	let processed = ref NodeSet.empty in

	let rec changeParentTo newParent node =

	  if not (Node.equal newParent !(parentOf newParent)) then
	    changeParentTo !(parentOf newParent) node
	  else
	    (let curParent = !(parentOf node) in
	     if not (Node.equal curParent newParent) then
	       
	       (let curParentChildren = !(childrenOf curParent) in
		let curParentChildrenCombedges =
		  NodeSet.fold (fun elm set -> NodeSet.union set !(combedgesOf elm))
		    curParentChildren NodeSet.empty
		in
		let newParentChildren = !(childrenOf newParent) in
		let newParentCombedges = !(combedgesOf newParent) in
		
		NodeSet.iter (fun n -> parentOf n := newParent) curParentChildren;
		childrenOf newParent := NodeSet.union newParentChildren curParentChildren ;
		combedgesOf newParent := NodeSet.union newParentCombedges curParentChildrenCombedges))
	in

	let rec visit stack node =

	  (* let _ = Printf.printf "START: %a\n(Stack %a)\n" printer_nodeinfo node printer_nodelist stack in *)
	  (* let _ = *)

	  if not (NodeSet.mem node !processed) then
	    
	    try
	      
	      let (inCycle, _, restOfStack), _ = ExtList.find_partition_index (Node.equal node) stack in
    	      inCycle |> List.iter (changeParentTo node)
		  
	    with ExtList.NotFoundPartition ->
	      
	      (let stack' = node :: stack in
	       edgesOf node
	          |> NodeSet.remove node
  		  |> NodeSet.iter (visit stack');
	       processed := NodeSet.add node !processed)
		
	  (* in *)
	  (* let _ = Printf.printf "END: %a\n" printer_nodeinfo node in *)
	  (* () *)
	    
	in

	dg.nodes |> List.iter (visit [])
	(* ; dg.nodes |> List.iter (Printf.printf "%a" printer_nodeinfo) *)

      in

      let get_coalesced_graph () =

	let cNodesSet = 

	  (* the coalesced nodes will be the equiv. class representatives (nodes with self as parent) *)
	     
	  dg.nodes |>
	    List.fold_left (fun cNodes node ->
	      if Node.equal node !(parentOf node) then
		NodeSet.add node cNodes
	      else
		cNodes)
	    NodeSet.empty
	in

	let cNodes = cNodesSet |> NodeSet.elements in
	
	let cEdges =

	  cNodes |>
	      List.fold_left (fun cEdges node ->
		 (* throw out edges that refer to non-coalesced nodes; that is, keep only edges to
		    coalesced nodes *)
		let cEdgesOfNode = NodeSet.inter !(combedgesOf node) cNodesSet in
		NodeMap.add node cEdgesOfNode cEdges)
	      NodeMap.empty

	in

	{ nodes = cNodes; edges = cEdges }

      in

      let _         = find_cycles () in
      let coalesced = get_coalesced_graph () in
      let tsort     = topo_sort coalesced in
      let result    = tsort |> List.map (fun x -> !(childrenOf x)) in

      (* Printf.printf "Final result: %a\n" (List.print ~first:"{" ~sep:";" ~last:"}" printer_nodeset) result ; *)
      result ;;


  end;;

(*
  
example code:

module M = Graph.Make(struct
  type t = int * string
  let compare (i1,_) (i2,_) = Stdlib.compare i1 i2
  let equal t1 t2 = compare t1 t2 == 0
  let hash (i,_) = Hashtbl.hash i
  let to_string (_,s) = s
  end) ;;

 let g = let open M in { nodes = [ 1,"term"; 2,"factor"; 3,"base"; 4,"digit" ] ;
    edges = [ (1, "term"), ( [ 2, "factor" ] |> List.enum |> NodeSet.of_enum ) ;
              (2, "factor"), ( [ 3, "base" ] |> List.enum |> NodeSet.of_enum ) ;
              (3, "base"), ( [ 1, "term" ; 4, "digit" ] |> List.enum |> NodeSet.of_enum ) ;
              (4, "digit"), ( [] |> List.enum |> NodeSet.of_enum )
            ]  |> List.enum |> NodeMap.of_enum } ;;

M.cyclic_topo_sort (M.reverse g);;

---

 should produce [[digit]; [term,factor,base]]

 *)

open Batteries;;

module Make :
  functor (Node : sig
    include Interfaces.OrderedType
    val to_string : t -> string
  end) ->
  sig

    module NodeSet : (Set.S with type elt = Node.t) ;;
    module NodeMap : (Map.S with type key = Node.t) ;;

    type dgraph = { nodes : Node.t list ; edges : NodeSet.t NodeMap.t } ;;

    val printer_node : 'a BatInnerIO.output -> Node.t -> unit
    val printer_nodeset : 'a BatInnerIO.output -> NodeSet.t -> unit
    val printer_nodelist : 'a BatInnerIO.output -> Node.t list -> unit

    val reverse : dgraph -> dgraph ;;
    val topo_sort : dgraph -> Node.t list ;;
    val cyclic_topo_sort : dgraph -> NodeSet.t list ;;
    
  end ;;

open GrammarCommon
open Proof
open TargetEnvms
open Type
open TypingCommon
open Utilities

(** Set of proofs that ignores initial flag *)
module ProofSet = Set.Make (struct
    type t = proof
    let compare = proof_compare true
  end)

(** Nonterminal and its typing. *)
type dfg_vertex = nt_ty
(** Positiveness of the edge, list of typings used in the proof, and the proof itself. *)
type dfg_edge = proof * bool
type dfg_path = (dfg_vertex * dfg_edge) list

(** Duplication Factor graph with typings of nonterminals (nt : ty) in vertices and edges to
    nonterminal typings used in one of proofs of that typing with boolean label whether the proof
    generated a new duplication factor (i.e., used typing of terminal a or had a duplication of a
    productive variable) or used a proof of typing of another nonterminal that was productive. *)
class dfg = object(self)
  (** List of edges to out-neighbours and either leaf proof or first proof for each vertex.
      Leaf proofs are proofs of nonterminal typings that do not use other nonterminals. First
      proof is the first typing the vertex had and is guaranteed to have a non-cyclic proof due
      to non-recursiveness of saturation iteration with respect to known nonterminal typings. *)
  val mutable graph : (dfg_edge NTTyMap.t * proof) NTTyMap.t = NTTyMap.empty

  (** List of in-neighbours of each vertex with label whether the edge is positive. *)
  val mutable rev_graph : NTTySet.t NTTyMap.t = NTTyMap.empty

  (** Adds edges from nt : ty to typings of used nonterminals and adds missing vertices. Returns
      whether an edge was added or updated. *)
  method add_vertex (proof : proof) : bool =
    let vertex = proof.derived in
    (* computing minimum of 2 and number of productive used nonterminals *)
    let pr_nts_count = NTTyMap.fold (fun vertex' locs acc ->
        (* when a productive nonterminal is used multiple times, it is counted as two *)
        acc + (HlocMap.sum locs) * int_of_bool (is_productive @@ snd vertex')
      ) proof.nt_assumptions 0
    in
    (* function to compute edge positiveness for given vertex *)
    let edge_pos_for_vertex (vertex' : dfg_vertex) : bool =
      proof.positive || pr_nts_count > 1 ||
      pr_nts_count = 1 && not @@ is_productive @@ snd vertex'
    in
    let out_vertices = NTTySet.set_of_map_keys proof.nt_assumptions in
    (* updating out edges of current vertex *)
    match NTTyMap.is_empty proof.nt_assumptions, NTTyMap.find_opt vertex graph with
    (* There are nonterminal dependencies, so adding missing edges and adding the vertex
       with first proof if it doesn't exist yet. *)
    | false, Some (out_edges, first) ->
      let updated : bool ref = ref false in
      (* computing new out_edges for vertex and new rev_graph *)
      let out_edges', rev_graph' =
        NTTySet.fold (fun vertex' (out_edges, rev_graph) ->
            let edge_pos = edge_pos_for_vertex vertex' in
            match edge_pos, NTTyMap.find_opt vertex' out_edges with
            | true, Some (_, false) ->
              (* updating the edge (but not reverse edge, since it already exists) if the edge
                 already exists but is not positive *)
              let edge = (proof, edge_pos) in
              let out_edges = NTTyMap.add vertex' edge out_edges in
              updated := true;
              (out_edges, rev_graph)
            | _, Some (_, true)
            | false, Some (_, false) ->
              (* doing nothing when edge already exists and has not lower positiveness *)
              (out_edges, rev_graph)
            | _, None ->
              (* creating the edge and reverse edge if it does not exist *)
              let edge = (proof, edge_pos) in
              let out_edges = NTTyMap.add vertex' edge out_edges in
              (* updating ingoing reverse edges from other vertices that should already
                 exist, being dependencies *)
              let in_edges = NTTyMap.find vertex' rev_graph in
              let rev_graph = rev_graph |> NTTyMap.add vertex' @@ NTTySet.add vertex in_edges in
              updated := true;
              (out_edges, rev_graph)
          ) out_vertices (out_edges, rev_graph)
      in
      if !updated then
        begin
          graph <- graph |> NTTyMap.add vertex (out_edges', first);
          rev_graph <- rev_graph'
        end;
      !updated
    | false, None ->
      (* there is no vertex yet *)
      let out_edges =
        (NTTyMap.of_seq @@
         Seq.map (fun vertex' ->
             (vertex',
              (proof, edge_pos_for_vertex vertex')
             )
           ) @@
         NTTySet.to_seq out_vertices,
         { proof with initial = true }
        )
      in
      graph <- NTTyMap.add vertex out_edges graph;
      (* updating ingoing reverse edges from other vertices that should already exist, being
         dependencies *)
      rev_graph <- NTTySet.fold (fun vertex' rev_graph ->
          let in_edges = NTTyMap.find vertex' rev_graph in
          NTTyMap.add vertex' (NTTySet.add vertex in_edges) rev_graph
        ) out_vertices rev_graph;
      (* adding new empty rev_graph vertex *)
      rev_graph <- NTTyMap.add vertex NTTySet.empty rev_graph;
      true
    (* there are no nonterminal dependencies, so adding a leaf proof if it does not exist yet
       or replacing the first proof with leaf proof *)
    | true, Some (out_edges, first) ->
      if NTTyMap.is_empty first.nt_assumptions then
        begin
          (* there already exists a vertex, but not a leaf proof *)
          graph <- NTTyMap.add vertex (out_edges, { proof with initial = true }) graph;
          false
        end
      else
        (* there already exists a leaf proof *)
        false
    | true, None ->
      (* there is no vertex yet *)
      graph <- NTTyMap.add vertex (NTTyMap.empty, { proof with initial = true }) graph;
      rev_graph <- NTTyMap.add vertex NTTySet.empty rev_graph;
      false

  method private complete_proof
      (path_to_cycle, cycle : dfg_edge list * dfg_edge list) : cycle_proof =
    let path_to_end_of_cycle = path_to_cycle @ cycle in
    (* marking vertices on the path as visited *)
    let visited : NTTySet.t ref =
      ref @@ NTTySet.of_list @@
      List.map (fun (proof, _) -> proof.derived) path_to_end_of_cycle
    in
    (* LIFO is used instead of FIFO because it produces better readability with relevant
       proofs next to each other, and there is only one solution when following first proofs
       anyway, so no need for bfs that finds shortest *)
    let queue : dfg_vertex Stack.t = Stack.create () in
    let add_to_queue_if_not_visited vertex =
      if not @@ NTTySet.mem vertex !visited then
        begin
          visited := NTTySet.add vertex !visited;
          Stack.push vertex queue
        end
    in
    (* gathering all proofs for vertices not on the path *)
    let proofs : proof list ref = ref @@ List.rev @@ List.map fst path_to_end_of_cycle in
    let proofs_set : ProofSet.t ref = ref @@ ProofSet.of_list !proofs in
    let add_proof (proof : proof) : unit =
      if not @@ ProofSet.mem proof !proofs_set then
        begin
          proofs := proof :: !proofs;
          proofs_set := ProofSet.add proof !proofs_set
        end
    in
    let cycle_vertices : NTTySet.t =
      NTTySet.of_list @@ List.map (fun (proof, _) -> proof.derived) cycle
    in
    (* Computing which of derivation trees of first proofs of one of cycle vertices
       is smallest amongst these that do not have a vertex from the cycle in the derivation
       tree. There must be at least one, because otherwise there would be a cycle in first
       proofs. *)
    let first_proof_tree_sizes = ref NTTyMap.empty in
    let rec first_proof_tree_size (vertex : dfg_vertex) : int =
      match NTTyMap.find_opt vertex !first_proof_tree_sizes with
      | Some s -> s
      | None ->
        let first : proof = snd @@ (NTTyMap.find vertex graph) in
        let res = NTTyMap.fold (fun vertex' _ acc ->
            if acc = -1 then
              acc
            else if NTTySet.mem vertex' cycle_vertices then
              -1
            else
              acc + first_proof_tree_size vertex'
          ) first.nt_assumptions 1
        in
        first_proof_tree_sizes := NTTyMap.add vertex res !first_proof_tree_sizes;
        res
    in
    let some_proof_from_cycle = fst @@ List.hd cycle in
    let escape_vertex = List.fold_left (fun (best_vertex, best_size) (proof, _) ->
        let vertex = proof.derived in
        let better_size = first_proof_tree_size vertex in
        if best_size = -1 || better_size != -1 && better_size < best_size then
          (vertex, better_size)
        else
          (best_vertex, best_size)
      ) (some_proof_from_cycle.derived, -1) cycle
    in
    assert (snd escape_vertex != -1);
    (* Found escape vertex, adding its proof to list of proofs and adding its dependencies
       to queue. Finding dependencies of escape vertex is different from the rest, since it
       may not stop at visited nodes that are on the path to the cycle (and is guaranteed to
       not stop at the cycle itself). *)
    (* TODO there is a chance of duplicated proof when path to cycle and proof of escape vertex
       have common edge *)
    let escape : proof = snd @@ NTTyMap.find (fst escape_vertex) graph in
    let rec add_escape_proof_tree proof =
      if not @@ NTTySet.mem proof.derived !visited then
        visited := NTTySet.add proof.derived !visited;
      add_proof proof;
      proof.nt_assumptions |> NTTyMap.iter (fun vertex' _ ->
          let first : proof = snd @@ (NTTyMap.find vertex' graph) in
          add_escape_proof_tree first
        )
    in
    add_escape_proof_tree escape;
    (* adding to queue all required nonterminals *)
    path_to_end_of_cycle |> List.iter (fun (proof, _) ->
        proof.nt_assumptions |>
        NTTyMap.iter (fun vertex _ ->
            if not @@ NTTySet.mem vertex !visited then
              add_to_queue_if_not_visited vertex
          )
      );
    (* Finding remaining proofs to complete all derivation trees. Some of them may end up
       pointing into typing from the cycle, but from previous analysis there is guaranteed
       escape vertex that has escapes from that cycle. No other cycle may form, as aside from
       path to cycle and cycle itself, all edges are from first proofs. *)
    while not @@ Stack.is_empty queue do
      let vertex = Stack.pop queue in
      (* finding outgoing edges, i.e., sets of nonterminals used in proofs of nonterminal typing
         in the vertex *)
      let first = snd @@ NTTyMap.find vertex graph in
      add_proof first;
      if not @@ NTTyMap.is_empty first.nt_assumptions then
        NTTySet.diff (NTTySet.set_of_map_keys first.nt_assumptions) !visited |>
        NTTySet.iter add_to_queue_if_not_visited
    done;
    (* it's more readable when following the order it was added in *)
    let proofs = List.rev !proofs in
    new cycle_proof path_to_cycle cycle escape proofs

  method private find_short_cycle_proof (start_vertex : dfg_vertex)
      (scc_roots : dfg_vertex NTTyMap.t) (vertex1 : dfg_vertex)
      (vertex2 : dfg_vertex) : cycle_proof =
    (* To make the proof short, a shortest path from start to vertex is found, then the positive
       edge to vertex' is added and then shortest cycle is found. *)
    let queue : dfg_vertex Queue.t = Queue.create () in
    Queue.push start_vertex queue;
    (* visited contains the vertex from which the vertex was visited in order to construct the
       path in the end. *)
    let visited : dfg_vertex NTTyMap.t ref =
      ref @@ NTTyMap.singleton start_vertex start_vertex in
    (* construct a path from start to given vertex based on visited. *)
    let rec backtrack vertex acc =
      if nt_ty_eq start_vertex vertex then
        start_vertex :: acc
      else
        backtrack (NTTyMap.find vertex !visited) (vertex :: acc)
    in
    while not @@ NTTyMap.mem vertex1 !visited do
      (* this should not fail if vertex1 is reachable *)
      let vertex = Queue.pop queue in
      (fst @@ NTTyMap.find vertex graph) |> NTTyMap.iter (fun vertex' _ ->
          if not @@ NTTyMap.mem vertex' !visited then
            begin
              visited := NTTyMap.add vertex' vertex !visited;
              Queue.push vertex' queue
            end
        )
    done;
    let path_to_vertex1 = backtrack vertex1 [] in
    let vertices_on_path_to_vertex1 = NTTySet.of_list path_to_vertex1 in
    let root = NTTyMap.find vertex1 scc_roots in
    let path : dfg_vertex list =
      if NTTySet.mem vertex2 vertices_on_path_to_vertex1 then
        (* already found a cycle, since a path to vertex1 was found with vertex2 on the way *)
        path_to_vertex1 @ [vertex2]
      else
        begin
          (* found a path from start_vertex to vertex1 - clearing visited from everything else and
             clearing the queue *)
          visited := !visited |> NTTyMap.filter (fun vertex _ ->
              NTTySet.mem vertex vertices_on_path_to_vertex1);
          Queue.clear queue;
          (* manually adding vertex2 as visited from vertex1 to include the positive edge *)
          visited := NTTyMap.add vertex2 vertex1 !visited;
          Queue.push vertex2 queue;
          let result : (dfg_vertex * dfg_vertex) option ref = ref None in
          while !result = None do
            (* this should not fail if there is a cycle containing vertex2 *)
            let vertex = Queue.pop queue in
            (fst @@ NTTyMap.find vertex graph) |> NTTyMap.iter (fun vertex' _ ->
                (* following only edges in the same SCC *)
                if nt_ty_eq root @@ NTTyMap.find vertex' scc_roots then
                  if NTTyMap.mem vertex' !visited then
                    begin
                      (* a cycle was found *)
                      if NTTySet.mem vertex' vertices_on_path_to_vertex1 then
                        (* a cycle containing the correct edge was found *)
                        result := Some (vertex, vertex')
                    end
                  else
                    begin
                      visited := NTTyMap.add vertex' vertex !visited;
                      Queue.push vertex' queue
                    end
              )
          done;
          let prev_last_vertex, last_vertex = option_get !result in
          (* constructing the path from start to end of cycle *)
          backtrack prev_last_vertex [] @ [last_vertex]
        end
    in
    (* adding inward edges on the path, except for the first (start) node, splitting the path
       into part leading to the cycle and the cycle itself *)
    let rec split_path (acc : dfg_edge list) (path : dfg_edge list) =
      match path with
      | (proof, _ as edge) :: path' ->
        if nt_ty_eq root @@ NTTyMap.find proof.derived scc_roots then
          split_path (edge :: acc) path'
        else
          (List.rev path, acc)
      | [] -> ([], acc)
    in
    let rec add_edges (acc : dfg_edge list) = function
      | vertex :: (next_vertex :: _ as vertices) ->
        let edge = (fst @@ NTTyMap.find vertex graph) |> NTTyMap.find next_vertex in
        add_edges (edge :: acc) vertices
      | [last_vertex] -> split_path [] acc
      | [] -> failwith "Unexpected empty path"
    in
    self#complete_proof @@ add_edges [] path
  
  (** DFS with checking for existence of positive edge in a cycle reachable from
      (start_nt, start_ty). Linear time, based on Kosaraju's algorithm.
      Returns cycle and its proofs with information on path from start to the cycle,
      then throughout the cycle, and escaping from cycle, along with required proofs. *)
  method find_positive_cycle
      (start_nt : nt_id) (start_ty : ty) : cycle_proof option =
    (* Computing the order of reverse traversal of the graph, but not starting from each
       vertex like in Kosaraju's algorithm, but only form (start_nt, start_ty), since
       we're only interested in vertices reachable from the start vertex. *)
    let start_vertex = (start_nt, start_ty) in
    if NTTyMap.mem start_vertex graph then
      begin
        let order : dfg_vertex list ref = ref [] in
        let visited : NTTySet.t ref = ref NTTySet.empty in
        let rec visit (vertex : dfg_vertex) : unit =
          if not @@ NTTySet.mem vertex !visited then
            begin
              visited := NTTySet.add vertex !visited;
              (* should exist *)
              let out_edges = fst @@ NTTyMap.find vertex graph in
              out_edges |> NTTyMap.iter (fun vertex' _ ->
                  visit vertex'
                );
              order := vertex :: !order
            end
        in
        visit start_vertex;
        (* Computing strongly connected components by reverse traversing of the graph, but only
           through the vertices that were visited (i.e., reachable from start). *)
        let scc_roots : dfg_vertex NTTyMap.t ref = ref NTTyMap.empty in
        let rec assign (vertex : dfg_vertex) (root : dfg_vertex) : unit =
          if not @@ NTTyMap.mem vertex !scc_roots then
            begin
              scc_roots := NTTyMap.add vertex root !scc_roots;
              (* should exist *)
              let in_edges = NTTyMap.find vertex rev_graph in
              in_edges |> NTTySet.iter (fun vertex' ->
                  if NTTySet.mem vertex' !visited then
                    assign vertex' root
                )
            end
        in
        !order |> List.iter (fun vertex ->
            assign vertex vertex
          );
        (* Computing the result by checking if any positive edge connects vertices from the same
           strongly connected component, i.e., is a part of a cycle. Note that it also works for
           self-loops. *)
        let cycle_data =
          NTTyMap.fold (fun vertex root acc ->
              NTTyMap.fold (fun vertex' (_, edge_pos) acc ->
                  if acc = None && edge_pos &&
                     nt_ty_eq root @@ NTTyMap.find vertex' !scc_roots then
                    (* We found an edge vertex -> vertex' that is a part of the positive cycle. We
                       save the root of this SCC and the vertices of the positive edge. *)
                    Some (root, vertex, vertex')
                  else
                    acc
                ) (fst @@ NTTyMap.find vertex graph) acc
            ) !scc_roots None
        in
        match cycle_data with
        | Some (root, vertex, vertex') ->
          Some (self#find_short_cycle_proof start_vertex !scc_roots vertex vertex')
        | None -> None
      end
    else
      (* when start vertex is not in the graph *)
      None

  (** The graph in printable form. *)
  method to_string (nt_name : nt_id -> string) : string =
    NTTyMap.fold (fun (nt, ty) (out_edges, _) acc ->
        let edges_str =
          String.concat "; " @@ NTTyMap.fold (fun (nt', ty') (_, edge_pos) acc ->
              (nt_name nt' ^ " : " ^ string_of_ty ty' ^ " (" ^
               string_of_int (int_of_bool edge_pos) ^ ")") :: acc
            ) out_edges []
        in
        acc ^ nt_name nt ^ " : " ^ string_of_ty ty ^ " => " ^ edges_str ^ "\n"
      ) graph ""
end

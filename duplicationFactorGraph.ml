open GrammarCommon
open HGrammar
open Proof
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
    productive variable) or used a proof of typing of another nonterminal that was productive.
    Proofs in DFG have identical values as in input aside from initial flag. *)
class dfg = object(self)
  (** List of edges to out-neighbours and either leaf proof or first proof for each vertex.
      Leaf proofs are proofs of nonterminal typings that do not use other nonterminals. First
      proof is the first typing the vertex had and is guaranteed to have a non-cyclic proof due
      to non-recursiveness of saturation iteration with respect to known nonterminal typings. *)
  val mutable graph : (dfg_edge NTTyMap.t * proof) NTTyMap.t = NTTyMap.empty

  (** List of in-neighbours of each vertex with label whether the edge is positive. *)
  val mutable rev_graph : NTTySet.t NTTyMap.t = NTTyMap.empty

  (* ----- adding vertices ----- *)
  
  (** Adds edges from nt : ty to typings of used nonterminals and adds missing vertices. Returns
      whether an edge was added or updated. *)
  method add_vertex (proof : proof) : bool =
    let vertex = proof.derived in
    (* computing minimum of 2 and number of productive used nonterminals *)
    let pr_nts_count : int = NTTyMap.fold (fun vertex' multi acc ->
        (* when a productive nonterminal is used multiple times, it is counted as two *)
        acc + (1 + int_of_bool multi) * int_of_bool (is_productive @@ snd vertex')
      ) proof.used_nts 0
    in
    (* function to compute edge positiveness for given vertex *)
    let edge_pos_for_vertex (vertex' : dfg_vertex) : bool =
      proof.positive || pr_nts_count > 1 ||
      pr_nts_count = 1 && not @@ is_productive @@ snd vertex'
    in
    let out_vertices = NTTySet.set_of_map_keys proof.used_nts in
    (* updating out edges of current vertex *)
    match NTTyMap.is_empty proof.used_nts, NTTyMap.find_opt vertex graph with
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
      if NTTyMap.is_empty first.used_nts then
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

  (* ----- searching for positive cycles ----- *)
  
  (** Computes strongly connected components in the subgraph with vertices reachable from
      start_vertex. Linear time, based on Kosaraju's algorithm. Empty result when start_vertex
      is not in the graph. *)
  method private reachable_sccs (start_vertex : dfg_vertex) : dfg_vertex NTTyMap.t =
    (* Computing the order of reverse traversal of the graph, but not starting from each
       vertex like in Kosaraju's algorithm, but only form start_vertex, since
       we're only interested in vertices reachable from the start vertex. *)
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
        !scc_roots
      end
    else
      (* when start vertex is not in the graph *)
      NTTyMap.empty

  (** Computing positive edges in cycles by checking if any positive edge connects vertices
      from the same strongly connected component, i.e., is a part of a cycle.
      Note that it also works for self-loops. *)
  method private find_positive_edges_in_cycles
      (scc_roots : dfg_vertex NTTyMap.t) : (dfg_vertex * dfg_vertex) list =
    NTTyMap.fold (fun vertex1 root acc ->
        NTTyMap.fold (fun vertex2 (_, edge_pos) acc ->
            if edge_pos && nt_ty_eq root @@ NTTyMap.find vertex2 scc_roots then
              (* We found an edge vertex -> vertex' that is a part of the positive cycle. We
                 save the root of this SCC and the vertices of the positive edge. *)
              (vertex1, vertex2) :: acc
            else
              acc
          ) (fst @@ NTTyMap.find vertex1 graph) acc
      ) scc_roots []

  (** Construct a path from vertex that loops on itself to start_vertex based on visited.
      This includes start_vertex and the looping vertex. If these were the same vertices, only
      one copy will be in the path. *)
  method private backtrack (start_vertex : dfg_vertex)
      (visited : dfg_vertex NTTyMap.t) : dfg_vertex list =
    let rec backtrack vertex acc =
      let source = NTTyMap.find vertex visited in
      if nt_ty_eq source vertex then
        vertex :: acc
      else
        backtrack source (vertex :: acc)
    in
    backtrack start_vertex []

  (** Produces (v1, edge v1->v2), ..., (vK, edge vK -> v(K+1)) from
      v1 -> v2 -> ... -> vK -> v(K+1). *)
  method private add_edges (vertices : dfg_vertex list) =
    let rec add_edges (acc : dfg_edge list) : dfg_vertex list -> dfg_edge list = function
      | vertex :: (next_vertex :: _ as vertices) ->
        let edge = (fst @@ NTTyMap.find vertex graph) |> NTTyMap.find next_vertex in
        add_edges (edge :: acc) vertices
      | [last_vertex] -> List.rev acc
      | [] -> failwith "Unexpected empty path"
    in
    add_edges [] vertices

  (** Finds a path from vertex2 to vertex1 of minimal length contained in a single SCC. *)
  method private find_short_cycle (scc_roots : dfg_vertex NTTyMap.t) (vertex1 : dfg_vertex)
      (vertex2 : dfg_vertex) : dfg_vertex list =
    let queue : dfg_vertex Queue.t = Queue.create () in
    Queue.push vertex2 queue;
    (* visited contains the vertex from which the vertex was visited. It is used to
       construct the path from start_vertex. Loop marks the beginning. *)
    let visited : dfg_vertex NTTyMap.t ref =
      ref @@ NTTyMap.singleton vertex2 vertex2 in
    let root = NTTyMap.find vertex2 scc_roots in
    (* BFS *)
    let searching = ref true in
    while !searching do
      (* this should not fail if there is a cycle containing vertex1 -> vertex2 *)
      let vertex = Queue.pop queue in
      (fst @@ NTTyMap.find vertex graph) |> NTTyMap.iter (fun vertex' _ ->
          (* following only edges in the same SCC *)
          if nt_ty_eq root @@ NTTyMap.find vertex' scc_roots then
            begin
              if not @@ NTTyMap.mem vertex' !visited then
                begin
                  visited := NTTyMap.add vertex' vertex !visited;
                  Queue.push vertex' queue
                end;
              (* checking also visited to take care of vertex1 = vertex2 *)
              if nt_ty_eq vertex1 vertex' then
                searching := false
            end
        )
    done;
    (* Either result was found, or exception was thrown (and algorithm is invalid).
       Constructing path from vertex2 to vertex1. *)
    self#backtrack vertex1 !visited

  (** Put the front of the lit with cycle at the end until it is equal to the expected first
      element. *)
  method private roll_cycle (cycle : dfg_edge list) (first : dfg_vertex) =
    let rec roll_cycle (es1 : dfg_edge list) (es2 : dfg_edge list) : dfg_edge list =
      match es1 with
      | (p, _) as e :: es ->
        if nt_ty_eq p.derived first then
          es1 @ List.rev es2
        else
          roll_cycle es @@ e :: es2
      | [] -> failwith "Expected a non-empty cycle that contains first"
    in
    roll_cycle cycle []

  (** Computes path o minimal length from start_vertex to one of vertices in cycle. The path
      includes exactly one vertex from the cycle, even if start_vertex is in cycle. *)
  method private find_path_to_cycle (start_vertex : dfg_vertex) (cycle : dfg_vertex list) =
    let queue : dfg_vertex Queue.t = Queue.create () in
    Queue.push start_vertex queue;
    (* visited contains the vertex from which the vertex was visited. It is used to construct the
       path from start_vertex. *)
    let visited : dfg_vertex NTTyMap.t ref =
      ref @@ NTTyMap.singleton start_vertex start_vertex in
    let cycle = NTTySet.of_list cycle in
    (* BFS *)
    let nearest_cycle_vertex = ref None in
    while !nearest_cycle_vertex = None do
      (* this should not fail if vertices from cycle are reachable *)
      let vertex = Queue.pop queue in
      if NTTySet.mem vertex cycle then
        (* detecting cycle member here takes care of start_vertex being in cycle *)
        nearest_cycle_vertex := Some vertex
      else
        (fst @@ NTTyMap.find vertex graph) |> NTTyMap.iter (fun vertex' _ ->
            if not @@ NTTyMap.mem vertex' !visited then
              begin
                visited := NTTyMap.add vertex' vertex !visited;
                Queue.push vertex' queue
              end
          )
    done;
    self#backtrack (option_get !nearest_cycle_vertex) !visited
  
  (** Recursively finds all necessary proofs of typings on given path to cycle and cycle.
      Tries to minimize the amount of additional proofs using heuristic approach. *)
  method private add_missing_proofs
      (path_to_cycle, cycle : dfg_edge list * dfg_edge list) : cycle_proof =
    let path_to_end_of_cycle = path_to_cycle @ cycle in
    (* marking vertices on the path as visited *)
    let visited : NTTySet.t ref =
      ref @@ NTTySet.of_list @@
      List.map (fun (proof, _) -> proof.derived) path_to_end_of_cycle
    in
    (* LIFO is used instead of FIFO because it produces better readability with relevant
       proofs next to each other, and there is only one solution when following first proofs
       anyway, so no need for BFS that finds the shortest. *)
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
          ) first.used_nts 1
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
       have common edge and the proof in the path to cycle is the same as initial *)
    let escape : proof = snd @@ NTTyMap.find (fst escape_vertex) graph in
    let rec add_escape_proof_tree proof =
      if not @@ NTTySet.mem proof.derived !visited then
        visited := NTTySet.add proof.derived !visited;
      add_proof proof;
      proof.used_nts |> NTTyMap.iter (fun vertex' _ ->
          let first : proof = snd @@ (NTTyMap.find vertex' graph) in
          add_escape_proof_tree first
        )
    in
    add_escape_proof_tree escape;
    (* adding to queue all required nonterminals *)
    path_to_end_of_cycle |> List.iter (fun (proof, _) ->
        proof.used_nts |>
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
      if not @@ NTTyMap.is_empty first.used_nts then
        NTTySet.diff (NTTySet.set_of_map_keys first.used_nts) !visited |>
        NTTySet.iter add_to_queue_if_not_visited
    done;
    (* it's more readable when following the order it was added in *)
    let proofs = List.rev !proofs in
    new cycle_proof path_to_cycle cycle escape proofs
  
  (** DFS with checking for existence of positive edge in a cycle reachable from
      (start_nt, start_ty).
      Returns cycle and its proofs with information on path from start to the cycle,
      then throughout the cycle, and escaping from cycle, along with required proofs. *)
  method find_positive_cycle
      (start_nt : nt_id) (start_ty : ty) : cycle_proof option =
    let start_vertex = (start_nt, start_ty) in
    let scc_roots = self#reachable_sccs start_vertex in
    let positive_cycle_edges = self#find_positive_edges_in_cycles scc_roots in
    match positive_cycle_edges with
    | (vertex1, vertex2) :: _ ->
      (* TODO iterate over each pair and take shortest by amount of proofs *)
      let cycle_vertices = self#find_short_cycle scc_roots vertex1 vertex2 in
      (* the extra vertex is dropped *)
      let cycle = self#add_edges @@ cycle_vertices @ [List.hd cycle_vertices] in
      let path_to_cycle_vertices = self#find_path_to_cycle start_vertex cycle_vertices in
      (* cycle vertex is dropped *)
      let path_to_cycle = self#add_edges path_to_cycle_vertices in
      (* cycle is correct, but has to be rolled over so that it begins with last element of
         path_to_cycle *)
      let cycle = self#roll_cycle cycle @@ last path_to_cycle_vertices in
      (* need to add proofs until no dependencies are missing *)
      let res = self#add_missing_proofs @@ (path_to_cycle, cycle) in
      Some res
    | [] -> None

  (* ----- printing ----- *)

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

open GrammarCommon
open TargetEnvms
open Type
open Utilities

(** Nonterminal and its typing. *)
type dfg_vertex = nt_ty
(** Positiveness of the edge, list of typings used in the proof, and the proof itself. *)
type dfg_edge = bool * used_nts * string
type dfg_path = (dfg_vertex * dfg_edge) list

let empty_dfg_edge : dfg_edge = (false, empty_used_nts, "")

let rec string_of_path (nt_name : nt_id -> string) (path : dfg_path) : string =
  let string_of_nt_ty (nt, ty : nt_ty) =
    nt_name nt ^ " : " ^ string_of_ty ty
  in
  match path with
  | [(nt_ty, _)] -> string_of_nt_ty nt_ty
  | (nt_ty, (positive, _, _)) :: path' ->
    let edge_str =
      if positive then
        "\n-- + -->\n"
      else
        "\n-- - -->\n"
    in
    string_of_nt_ty nt_ty ^ edge_str ^ string_of_path nt_name path'
  | [] -> failwith "Unexpected empty path"

module NTTySet = Set.Make (struct
    type t = nt_ty
    let compare = nt_ty_compare
  end)

(** Duplication Factor graph with typings of nonterminals (nt : ty) in vertices and edges to
    nonterminal typings used in one of proofs of that typing with boolean label whether the proof
    generated a new duplication factor (i.e., used typing of terminal a or had a duplication of a
    productive variable) or used a proof of typing of another nonterminal that was productive. *)
class dfg = object(self)
  (** List of out-neighbours of each vertex. *)
  val mutable graph : (dfg_edge NTTyMap.t) NTTyMap.t = NTTyMap.empty

  (** List of in-neighbours of each vertex with label whether the edge is positive. *)
  val mutable rev_graph : NTTySet.t NTTyMap.t = NTTyMap.empty

  method private get_or_create_edges (vertex : nt_id * ty) =
    match NTTyMap.find_opt vertex graph, NTTyMap.find_opt vertex rev_graph with
    | Some edges1, Some edges2 -> (edges1, edges2)
    | _, _ ->
      let out_edges = NTTyMap.empty in
      graph <- NTTyMap.add vertex out_edges graph;
      let in_edges = NTTySet.empty in
      rev_graph <- NTTyMap.add vertex in_edges rev_graph;
      (out_edges, in_edges)

  method private replace_edge (vertex_from : dfg_vertex) (vertex_to : dfg_vertex)
      (edge : dfg_edge) : unit =
    let out_edges, _ = self#get_or_create_edges vertex_from in
    graph <- NTTyMap.add vertex_from (NTTyMap.add vertex_to edge out_edges) graph;
    let _, in_edges = self#get_or_create_edges vertex_to in
    rev_graph <- NTTyMap.add vertex_to (NTTySet.add vertex_from in_edges) rev_graph

  (** Adds edges from nt : ty to typings of used nonterminals and adds missing vertices. Returns
      whether an edge was added or updated. *)
  method add_vertex (nt : nt_id) (ty : ty) (used_nts : used_nts)
      (positive : bool) (proof : string) : bool =
    let vertex = (nt, ty) in
    (* computing minimum of 2 and number of productive used nonterminals *)
    let pr_nts_count = NTTyMap.fold (fun vertex' multi acc ->
        (* when a productive nonterminal is used multiple times, it is counted as two *)
        acc + (1 + int_of_bool multi) * int_of_bool (is_productive @@ snd vertex')
      ) used_nts 0
    in
    (* updating out edges of current vertex *)
    let updated : bool ref = ref false in
    let out_edges, _ = self#get_or_create_edges vertex in
    used_nts |> NTTyMap.iter (fun vertex' _ ->
        match NTTyMap.find_opt vertex' out_edges with
        | Some (false, _, _) ->
          (* updating the edge and reverse edge if the edge already exists *)
          let edge =
            positive || pr_nts_count > 1 ||
            pr_nts_count = 1 && not @@ is_productive @@ snd vertex'
          in
          if edge then
            begin
              self#replace_edge vertex vertex' (edge, used_nts, proof);
              updated := true
            end
        | Some (true, _, _) -> ()
        | None ->
          let edge =
            positive || pr_nts_count > 1 ||
            pr_nts_count = 1 && not @@ is_productive @@ snd vertex'
          in
          self#replace_edge vertex vertex' (edge, used_nts, proof);
          updated := true
      );
    !updated

  method private find_short_cycle_path (start_vertex : dfg_vertex)
      (scc_roots : dfg_vertex NTTyMap.t) (vertex1 : dfg_vertex)
      (vertex2 : dfg_vertex) : dfg_path =
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
      NTTyMap.find vertex graph |> NTTyMap.iter (fun vertex' _ ->
          if not @@ NTTyMap.mem vertex' !visited then
            begin
              visited := NTTyMap.add vertex' vertex !visited;
              Queue.push vertex' queue
            end
        )
    done;
    let path_to_vertex1 = backtrack vertex1 [] in
    let vertices_on_path_to_vertex1 = NTTySet.of_list path_to_vertex1 in
    let path =
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
          let root = NTTyMap.find vertex1 scc_roots in
          while !result = None do
            (* this should not fail if there is a cycle containing vertex2 *)
            let vertex = Queue.pop queue in
            NTTyMap.find vertex graph |> NTTyMap.iter (fun vertex' _ ->
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
    (* adding inward edges on the path, except for the first (start) node *)
    let rec add_edges acc = function
      | vertex :: ((next_vertex :: _) as vertices) ->
        add_edges
          ((vertex, NTTyMap.find vertex graph |> NTTyMap.find next_vertex) :: acc)
          vertices
      | [last_vertex] -> List.rev_append acc [(last_vertex, empty_dfg_edge)]
      | [] -> failwith "Unexpected empty path"
    in
    add_edges [] path

  (** DFS with checking for existence of positive edge in a cycle reachable from
      (start_nt, start_ty). Linear time, based on Kosaraju's algorithm.
      Returns path from start to end of cycle if found in the form of list of vertices
      and boolean whether the edge leading to them is positive (false for start vertex). *)
  method find_positive_cycle (start_nt : nt_id) (start_ty : ty) : dfg_path option =
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
              let out_edges = NTTyMap.find vertex graph in
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
              NTTyMap.fold (fun vertex' (edge, _, _) acc ->
                  if acc = None && edge &&
                     nt_ty_eq root @@ NTTyMap.find vertex' !scc_roots then
                    (* We found an edge vertex -> vertex' that is a part of the positive cycle. We
                       save the root of this SCC and the vertices of the positive edge. *)
                    Some (root, vertex, vertex')
                  else
                    acc
                ) (NTTyMap.find vertex graph) acc
            ) !scc_roots None
        in
        match cycle_data with
        | Some (root, vertex, vertex') ->
          Some (self#find_short_cycle_path start_vertex !scc_roots vertex vertex')
        | None -> None
      end
    else
      (* when start vertex is not in the graph *)
      None

  method get_proofs_on_path (path : dfg_path) : string list =
    List.filter (fun s -> s <> "") @@
    List.map (fun (_, (_, _, proof)) -> proof) @@
    path

  method get_required_proofs (path : dfg_path) : string list =
    (* marking vertices on the path as visited *)
    let visited : NTTySet.t ref =
      ref @@ NTTySet.of_list @@ List.map fst path
    in
    let count_unvisited_nts (used_nts : used_nts) : int =
      NTTyMap.fold (fun nt_ty _ acc ->
          if NTTySet.mem nt_ty !visited then
            acc
          else
            acc + 1
        ) used_nts 0
    in
    (* adding to queue all required nonterminals *)
    let queue : nt_ty Queue.t = Queue.create () in
    path |> List.iter (fun (_, (_, used_nts, _)) ->
        used_nts |> NTTyMap.iter (fun nt_ty _ ->
            if not @@ NTTySet.mem nt_ty !visited then
              begin
                visited := NTTySet.add nt_ty !visited;
                Queue.push nt_ty queue
              end
          )
      );
    (* gathering proofs for vertices not on the path *)
    let res : string list ref = ref [] in
    while not @@ Queue.is_empty queue do
      let vertex = Queue.pop queue in
      (* finding outgoing edges, i.e., sets of nonterminals used in proofs of nonterminal typing
         in the vertex *)
      let edges = NTTyMap.find vertex graph in
      match NTTyMap.bindings edges with
      | (_, (_, some_used_nts, some_proof)) :: edges' ->
        (* Any of edges is sufficient to get a proof, so taking the one with least amount of
           unvisited vertices as a heuristic to get small amount of short proofs. *)
        let _, best_used_nts, best_proof =
          List.fold_left (fun ((min_count, _, _) as acc) (_, (_, used_nts, proof)) ->
              let c = count_unvisited_nts used_nts in
              if c < min_count then
                (c, used_nts, proof)
              else
                acc
            ) (count_unvisited_nts some_used_nts, some_used_nts, some_proof) edges'
        in
        (* Found a proof with least amount of unvisited vertices. Adding these vertices to the
           queue and the proof to the result. *)
        res := best_proof :: !res;
        NTTyMap.to_seq best_used_nts |> Seq.iter (fun (nt_ty, _) ->
            if not @@ NTTySet.mem nt_ty !visited then
              begin
                visited := NTTySet.add nt_ty !visited;
                Queue.push nt_ty queue
              end
          )
      | [] -> ()
    done;
    !res

  (** The graph in printable form. *)
  method to_string (string_of_nt : nt_id -> string) : string =
    NTTyMap.fold (fun (nt, ty) out_edges acc ->
        let edges_str =
          String.concat "; " @@ NTTyMap.fold (fun (nt', ty') (edge, _, _) acc ->
              (string_of_nt nt' ^ " : " ^ string_of_ty ty' ^ " (" ^
               string_of_int (int_of_bool edge) ^ ")") :: acc
            ) out_edges []
        in
        acc ^ string_of_nt nt ^ " : " ^ string_of_ty ty ^ " -> " ^ edges_str ^ "\n"
      ) graph ""
end

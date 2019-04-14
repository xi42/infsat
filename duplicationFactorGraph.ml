open GrammarCommon
open TargetEnvms
open Type
open Utilities

type dfg_vertex = nt_ty

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
  val mutable graph : (bool NTTyMap.t) NTTyMap.t = NTTyMap.empty

  (** List of in-neighbours of each vertex with label whether the edge is positive. *)
  val mutable rev_graph : (bool NTTyMap.t) NTTyMap.t = NTTyMap.empty

  method private get_or_create_edges (vertex : nt_id * ty) =
    match NTTyMap.find_opt vertex graph, NTTyMap.find_opt vertex rev_graph with
    | Some edges1, Some edges2 -> (edges1, edges2)
    | _, _ ->
      let out_edges = NTTyMap.empty in
      graph <- NTTyMap.add vertex out_edges graph;
      let in_edges = NTTyMap.empty in
      rev_graph <- NTTyMap.add vertex in_edges rev_graph;
      (out_edges, in_edges)

  method replace_edge (vertex_from : dfg_vertex) (vertex_to : dfg_vertex) (edge : bool) : unit =
    let out_edges, _ = self#get_or_create_edges vertex_from in
    graph <- NTTyMap.add vertex_from (NTTyMap.add vertex_to edge out_edges) graph;
    let _, in_edges = self#get_or_create_edges vertex_to in
    rev_graph <- NTTyMap.add vertex_to (NTTyMap.add vertex_from edge in_edges) rev_graph

  (** Adds edges from nt : ty to typings of used nonterminals and adds missing vertices. Returns
      whether an edge was added or updated. *)
  method add_vertex (nt : nt_id) (ty : ty) (used_nts : used_nts) (positive : bool) : bool =
    let vertex = (nt, ty) in
    (* computing minimum of 2 and number of productive used nonterminals *)
    let pr_nts_count = NTTyMap.fold (fun vertex' multi acc ->
        (* when a productive nonterminal is used multiple times, it is counted as two *)
        acc + (1 + int_of_bool multi) * int_of_bool (is_productive @@ snd vertex')
      ) used_nts 0
    in
    (* updating out edges of current vertex *)
    let out_edges, _ = self#get_or_create_edges vertex in
    used_nts |> NTTyMap.exists (fun vertex' _ ->
        match NTTyMap.find_opt vertex' out_edges with
        | Some false ->
          (* updating the edge and reverse edge if the edge already exists *)
          let edge =
            positive || pr_nts_count > 1 ||
            pr_nts_count = 1 && not @@ is_productive @@ snd vertex'
          in
          if edge then
            begin
              self#replace_edge vertex vertex' edge;
              true
            end
          else
            false
        | Some true -> false
        | None ->
          let edge =
            positive || pr_nts_count > 1 ||
            pr_nts_count = 1 && not @@ is_productive @@ snd vertex'
          in
          self#replace_edge vertex vertex' edge;
          true
      )

  (** DFS with checking for existence of positive edge in a cycle reachable from
      (start_nt, start_ty). Linear time, based on Kosaraju's algorithm. *)
  method has_positive_cycle (start_nt : nt_id) (start_ty : ty) : bool =
    (* Computing the order of reverse traversal of the graph, but not starting from each vertex like
       in Kosaraju's algorithm, but only form (start_nt, start_ty), since we're only interested in
       vertices reachable from the start vertex. *)
    let start_vertex = (start_nt, start_ty) in
    let order : dfg_vertex list ref = ref [] in
    let visited : NTTySet.t ref = ref NTTySet.empty in
    let rec visit (vertex : nt_id * ty) : unit =
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
    try
      visit start_vertex;
      (* Computing strongly connected components by reverse traversing of the graph, but only
         through the vertices that were visited (i.e., reachable from start). *)
      let scc_root : dfg_vertex NTTyMap.t ref = ref NTTyMap.empty in
      let rec assign (vertex : dfg_vertex) (root : dfg_vertex) : unit =
        if not @@ NTTyMap.mem vertex !scc_root then
          begin
            scc_root := NTTyMap.add vertex root !scc_root;
            (* should exist *)
            let in_edges = NTTyMap.find vertex rev_graph in
            in_edges |> NTTyMap.iter (fun vertex' _ ->
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
      NTTyMap.fold (fun vertex root acc ->
          acc || NTTyMap.fold (fun vertex' edge acc ->
              acc || edge && nt_ty_compare root (NTTyMap.find vertex' !scc_root) = 0
            ) (NTTyMap.find vertex graph) false
        ) !scc_root false
    with
    | Not_found ->
      (* when start vertex is not in the graph *)
      false

  (** The graph in printable form. *)
  method to_string (string_of_nt : nt_id -> string) : string =
    NTTyMap.fold (fun (nt, ty) out_edges acc ->
        let edges_str =
          String.concat "; " @@ NTTyMap.fold (fun (nt', ty') edge acc ->
              (string_of_nt nt' ^ " : " ^ string_of_ty ty' ^ " (" ^
               string_of_int (int_of_bool edge) ^ ")") :: acc
            ) out_edges []
        in
        acc ^ string_of_nt nt ^ " : " ^ string_of_ty ty ^ " -> " ^ edges_str ^ "\n"
      ) graph ""
end

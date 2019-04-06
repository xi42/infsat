open GrammarCommon
open TargetEnvListMap
open Type
open Utilities

type dfg_vertex = nt_id * ty

let dfg_vertex_eq (nt1, ty1) (nt2, ty2) = nt1 = nt2 && eq_ty ty1 ty2

module DFGVertexHash = Hashtbl.Make(struct
    type t = dfg_vertex
    let hash (nt, ty) = Hashtbl.hash (nt, id_of_ty ty)
    let equal = dfg_vertex_eq
  end)

(** Duplication Factor graph with typings of nonterminals (nt : ty) in vertices and edges to
    nonterminal typings used in one of proofs of that typing with boolean label whether the proof
    generated a new duplication factor (i.e., used typing of terminal a or had a duplication of a
    productive variable) or used a proof of typing of another nonterminal that was productive. *)
class dfg = object(self)
  (** List of out-neighbours of each vertex. *)
  val graph : (bool DFGVertexHash.t) DFGVertexHash.t = DFGVertexHash.create 8192

  (** List of in-neighbours of each vertex with label whether the edge is positive. *)
  val rev_graph : (bool DFGVertexHash.t) DFGVertexHash.t = DFGVertexHash.create 8192

  method private get_or_create_edges (vertex : nt_id * ty) =
    try
      (DFGVertexHash.find graph vertex, DFGVertexHash.find rev_graph vertex)
    with
    | Not_found ->
      let out_edges = DFGVertexHash.create 8192 in
      DFGVertexHash.add graph vertex out_edges;
      let in_edges = DFGVertexHash.create 8192 in
      DFGVertexHash.add rev_graph vertex in_edges;
      (out_edges, in_edges)
  
  method register_vertex (nt : nt_id) (ty : ty) (used_nts : NTTypings.t) (positive : bool) : unit =
    let vertex = (nt, ty) in
    (* computing minimum of 2 and number of productive used nonterminals *)
    let pr_nts = NTTypings.fold_left_short_circuit 0 used_nts 2 (fun acc vertex' ->
        acc + int_of_bool (is_productive @@ snd vertex')
      ) in
    (* updating out edges of current vertex *)
    let out_edges, _ = self#get_or_create_edges vertex in
    used_nts |> NTTypings.iter (fun vertex' ->
        try
          (* updating the edge and reverse edge if the edge already exists *)
          if not @@ DFGVertexHash.find out_edges vertex' then
            begin
              let edge =
                positive || pr_nts > 1 || pr_nts = 1 && not @@ is_productive @@ snd vertex'
              in
              DFGVertexHash.replace out_edges vertex' edge;
              (* should exist *)
              DFGVertexHash.replace (DFGVertexHash.find rev_graph vertex') vertex edge
            end
        with
        | Not_found ->
          let edge =
            positive || pr_nts > 1 || pr_nts = 1 && not @@ is_productive @@ snd vertex'
          in
          DFGVertexHash.replace out_edges vertex' edge;
          let _, in_edges = self#get_or_create_edges vertex' in
          DFGVertexHash.add in_edges vertex edge
      )

  (** DFS with checking for existence of positive edge in a cycle reachable from
      (start_nt, start_ty). Linear time, based on Kosaraju's algorithm. *)
  method has_positive_cycle (start_nt : nt_id) (start_ty : ty) : bool =
    (* Computing the order of reverse traversal of the graph, but not starting from each vertex like
       in Kosaraju's algorithm, but only form (start_nt, start_ty), since we're only interested in
       vertices reachable from the start vertex. *)
    let start_vertex = (start_nt, start_ty) in
    let order : dfg_vertex list ref = ref [] in
    let visited : unit DFGVertexHash.t = DFGVertexHash.create 8192 in
    let rec visit (vertex : nt_id * ty) : unit =
      if not @@ DFGVertexHash.mem visited vertex then
        begin
          DFGVertexHash.add visited vertex ();
          (* should exist *)
          let out_edges = DFGVertexHash.find graph vertex in
          out_edges |> DFGVertexHash.iter (fun vertex' _ ->
              visit vertex'
            );
          order := vertex :: !order
        end
    in
    try
      visit start_vertex;
      (* Computing strongly connected components by reverse traversing of the graph, but only
         through the vertices that were visited (i.e., reachable from start). *)
      let scc_root : dfg_vertex DFGVertexHash.t = DFGVertexHash.create 8192 in
      let rec assign (vertex : dfg_vertex) (root : dfg_vertex) : unit =
        if not @@ DFGVertexHash.mem scc_root vertex then
          begin
            DFGVertexHash.add scc_root vertex root;
            (* should exist *)
            let in_edges = DFGVertexHash.find rev_graph vertex in
            in_edges |> DFGVertexHash.iter (fun vertex' _ ->
                if DFGVertexHash.mem visited vertex' then
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
      DFGVertexHash.fold (fun vertex root acc ->
          acc || DFGVertexHash.fold (fun vertex' edge acc ->
              acc || edge && dfg_vertex_eq root (DFGVertexHash.find scc_root vertex')
            ) (DFGVertexHash.find graph vertex) false
        ) scc_root false
    with
    | Not_found ->
      (* when start vertex is not in the graph *)
      false

  (** The graph in printable form. *)
  method to_string : string =
    DFGVertexHash.fold (fun (nt, ty) out_edges acc ->
        let edges_str =
          String.concat "; " @@ DFGVertexHash.fold (fun (nt', ty') edge acc ->
              (string_of_int nt' ^ " : " ^ string_of_ty ty' ^ " (" ^
               string_of_int (int_of_bool edge) ^ ")") :: acc
            ) out_edges []
        in
        acc ^ string_of_int nt ^ " : " ^ string_of_ty ty ^ " -> " ^ edges_str ^ "\n"
      ) graph ""
end

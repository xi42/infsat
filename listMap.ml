module type OrderedKeyValue = sig
  type k
  type v
  val compare_k : k -> k -> int
  val compare_v : v -> v -> int
end

module type SL = sig
  type k
  type v
  type t

  val empty : t
  val singleton : k -> v -> t
  val of_list : (k * v list) list -> t
  val to_list : t -> (k * v list) list
    
  val mem : k -> t -> bool
  val is_empty : t -> bool

  val merge : t -> t -> t

  val to_string : (k -> string) -> (v -> string) -> t -> string
end

module Make (KV : OrderedKeyValue) =
struct
  module VL = SortedList.Make(struct
      type t = KV.v
      let compare = KV.compare_v
    end)

  module KVL = SortedList.Make(struct
      type t = KV.k * VL.t
      let compare (k1, _) (k2, _) = KV.compare_k k1 k2
    end)

  type t = KVL.t

  (* construction *)
        
  let empty = KVL.empty
      
  let singleton k v = KVL.singleton (k, VL.singleton v)

  let of_list l = KVL.of_list @@ List.map (fun (k, vl) -> (k, VL.of_list vl)) l

  let to_list = KVL.map (fun (k, vl) -> (k, VL.to_list vl))

  (* basic operations *)
  
  let mem k m = KVL.exists (fun (k', _) -> KV.compare_k k k' = 0) m

  let is_empty m = KVL.is_empty m

  (* splitting, filtering, and joining *)

  let merge =
    KVL.merge_custom (fun (k1, vl1) (_, vl2) -> (k1, VL.merge vl1 vl2))
        
  let for_all f m = m |> KVL.for_all (fun (k, vl) -> vl |> VL.for_all (fun v -> f k v))
  
  let exists f m = m |> KVL.exists (fun (k, vl) -> vl |> VL.exists (fun v -> f k v))

  (* pretty printing *)

  let to_string k_to_string v_to_string m =
    Utilities.string_of_list Utilities.id @@
    KVL.map (fun (k, v) -> k_to_string k ^ " -> " ^ v_to_string v) m
end

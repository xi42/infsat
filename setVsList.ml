(* A simple application that tests if sorted lists are considerably faster than sets when merging
   for small sizes. It turns out they are by around 50-100%, especially for smaller sizes, and this
   is including large common constant overhead. Iteration is around 20% faster on lists too.
   ocamlopt -inline 1000 -o set_vs_list flags.ml utilities.ml profiling.ml sortedList.ml set_vs_list.ml *)

open Utilities
open Profiling

let n = 4000
let k = 10
let m = 5

module IntSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = int
  end)

module SortedInts = SortedList.Make(struct
    let compare = Pervasives.compare
    type t = int
  end)

let lists = List.map (fun _ -> SortedInts.uniq (SortedInts.init (fun _ -> Random.int m) k)) (fromto 1 n)

let sets = List.map (fun l -> IntSet.of_list (SortedInts.to_list l)) lists

let _ =
  Flags.debugging := true;
  profile "list merge" (fun () ->
      List.iter (fun a ->
          List.iter (fun b ->
              SortedInts.merge a b; ()
            ) lists
        ) lists
    );
  profile "set merge" (fun () ->
      List.iter (fun a ->
          List.iter (fun b ->
              IntSet.union a b; ()
            ) sets
        ) sets
    );
  profile "list iteration" (fun () ->
      List.iter (fun a ->
          List.iter (fun b ->
              SortedInts.iter (fun _ -> ()) b; ()
            ) lists
        ) lists
    );
  profile "set iteration" (fun () ->
      List.iter (fun a ->
          List.iter (fun b ->
              IntSet.iter (fun _ -> ()) b; ()
            ) sets
        ) sets
    );
  report_timings 0.0 0.0
              

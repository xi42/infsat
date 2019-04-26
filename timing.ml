open Utilities

let timings : (string * float) list ref = ref []

let add_timing name time =
  timings := (name, time)::!timings

let time (name : string) (f : unit -> 'a) : 'a =
  let start_t = Sys.time() in
  print_verbose !Flags.verbose_profiling @@ lazy (
    "\n--------======== " ^ name ^ " ========--------\n"
  );
  let res = f() in
  let end_t = Sys.time() in
  (add_timing name (end_t -. start_t);
   res)

let report_timings start_t end_t =
  print_verbose !Flags.verbose_profiling @@ lazy (
    let total_timings = List.fold_left (fun acc (_, time) -> acc +. time) 0.0 !timings in
    let other_time = max 0.0 @@ end_t -. start_t -. total_timings in
    "\nElapsed Time: " ^ string_of_float (end_t -. start_t) ^ "s\n" ^
    (List.rev !timings |> concat_map "\n" (fun (name, time) ->
         "  " ^ name ^ ": " ^ string_of_float time ^ "s"
       )) ^
    "  other: " ^ string_of_float other_time ^ "s"
  )

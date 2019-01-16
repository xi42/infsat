let timings = ref []

let add_timing name time =
  timings := (name, time)::!timings

let profile name f =
  let start_t = Sys.time() in
  let res = f() in
  let end_t = Sys.time() in
  (add_timing name (end_t -. start_t);
   res)

let report_timings start_t end_t =
  print_string ("Elapsed Time: "^(string_of_float (end_t -. start_t))^"s\n");
  if !Flags.debugging then (
    List.iter (fun (name, time) ->
        print_string ("  "^name^": "^(string_of_float time)^"s\n")
      ) (List.rev !timings);
    let total_timings = List.fold_left (fun acc (_, time) -> acc +. time) 0.0 !timings in
    let other_time = end_t -. start_t -. total_timings in
    print_string ("  other: "^(string_of_float other_time)^"s\n")
  ) else
    ()

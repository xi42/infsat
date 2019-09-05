type 'a t = int list ref * 'a list array

let make (max_first : int) : 'a t =
  (ref [], Array.make (max_first + 1) [])

let enqueue (firsts, seconds : 'a t) (first : int) (second : 'a) : unit =
  let sec = seconds.(first) in
  seconds.(first) <- second :: sec;
  if sec = [] then
    firsts := first :: !firsts

exception Empty

let dequeue (firsts, seconds : 'a t) : int * 'a =
  match !firsts with
  | [] -> raise_notrace Empty
  | first :: firsts' ->
    match seconds.(first) with
    | [] -> failwith "Empty seconds."
    | second :: sec ->
      seconds.(first) <- sec;
      if sec = [] then
        firsts := firsts';
      (first, second)

let remove_all (firsts, seconds : 'a t) (first : int) : unit =
  match seconds.(first) with
  | [] -> ()
  | _ ->
    seconds.(first) <- [];
    firsts := !firsts |> List.filter (fun first' -> first' <> first)

let size (firsts, seconds : 'a t) : int =
  List.fold_left (fun acc first ->
      acc + (List.length seconds.(first))
    ) 0 !firsts

let string_of_queue (s : 'a -> string) (firsts, seconds : 'a t) : string =
  Utilities.string_of_list Utilities.id @@
  List.map (fun first ->
      string_of_int first ^ " -> " ^ (String.concat ", " @@ List.map s seconds.(first))
    ) !firsts

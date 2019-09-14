type 'a t = int list ref * 'a list array

let make (max_first : int) : 'a t =
  (ref [], Array.make (max_first + 1) [])

let enqueue (firsts, seconds : 'a t) (first : int) (second : 'a) : unit =
  let sec = seconds.(first) in
  if sec = [] then
    firsts := first :: !firsts;
  seconds.(first) <- second :: sec

exception Empty

let dequeue (firsts, seconds : 'a t) : int * 'a list =
  match !firsts with
  | [] -> raise_notrace Empty
  | first :: firsts' ->
    firsts := firsts';
    let sec = seconds.(first) in
    seconds.(first) <- [];
    (first, sec)

let size (firsts, seconds : 'a t) : int =
  List.length !firsts

let string_of_queue (s : 'a -> string) (firsts, seconds : 'a t) : string =
  Utilities.string_of_list Utilities.id @@
  List.map (fun first ->
      string_of_int first ^ " -> " ^ (String.concat ", " @@ List.map s seconds.(first))
    ) !firsts

type 'a t = int list ref * 'a list array

let make (max_first : int) : 'a t =
  (ref [], Array.make (max_first + 1) [])

let enqueue (firsts, seconds : 'a t) (first : int) (second : 'a) : unit =
  let sec = seconds.(first) in
  seconds.(first) <- second :: sec;
  if sec = [] then
    firsts := first :: !firsts

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

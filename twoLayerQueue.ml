type 'a t = int list ref * 'a list array

let mk_queue (max_first : int) : 'a t =
  (ref [], Array.make (max_first + 1) [])

let enqueue ((firsts, seconds) : 'a t) (first : int) (second : 'a) : unit =
  let sec = seconds.(first) in
  begin
    seconds.(first) <- second::sec;
    if sec = [] then
      firsts := first::!firsts
  end

exception EmptyQueue

let dequeue ((firsts, seconds) : 'a t) : int * 'a =
  match !firsts with
  | [] -> raise EmptyQueue
  | first::firsts' ->
    match seconds.(first) with
    | [] -> failwith "Empty seconds"
    | second::sec ->
      seconds.(first) <- sec;
      if sec = [] then
        firsts := firsts';
      (first, second)

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

let dequeue ((firsts, seconds) : 'a t) : int * 'a list =
  match !firsts with
  | [] -> raise EmptyQueue
  | first::firsts' ->
    firsts := firsts';
    let sec = seconds.(first) in
    begin
      seconds.(first) <- [];
      (first, sec)
    end


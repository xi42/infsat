type t = int list ref * bool array

exception Empty

(** Empty LIFO queue for values from 0 to n-1. *)
let make n : t = (ref [], Array.make n false)

(** LIFO queue filled with values from 0 to n-1, with 0 on the top. *)
let makeall n : t = (ref (Utilities.range 0 n), Array.make n true)

(** Dequeues an integer or raises Empty. *)
let rec dequeue (qref, bitmap) =
  match !qref with
  | [] -> raise_notrace Empty
  | n :: ns ->
    qref := ns;
    if bitmap.(n) then
      begin
        bitmap.(n) <- false;
        n
      end
    else
      (* should not happen unless made with duplicates in make_fromlist, then the duplicates
         are ignored and only the topmost value is used. *)
      dequeue (qref, bitmap)

(** Enqueues an integer if it isn't in the queue yet. *)
let enqueue (qref, bitmap) n =
  if bitmap.(n) = false then
    qref := n :: !qref;
  bitmap.(n) <- true

let is_empty queue =
  try
    let n = dequeue queue in
    enqueue queue n;
    false
  with
  | Empty -> true 

(** Iterates over the queue by dequeuing integers until it is empty. *)
let rec iter f queue =
  try
    let x = dequeue queue in
    f x;
    iter f queue
  with
  | Empty -> ()

let size (qref, bitmap : t) : int =
  List.length !qref

let string_of_queue (qref, bitmap : t) : string =
  Utilities.string_of_list string_of_int !qref

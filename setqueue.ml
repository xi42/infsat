type t = int list ref * bool array

exception Empty

(** Empty LIFO queue for values from 0 to n-1. *)
let make n = (ref [], Array.make n false)

(** LIFO queue filled with values from 0 to n-1, with 0 on the top. *)
let makeall n = (ref (Utilities.fromto 0 n), Array.make n true)

(** Creates LIFO queue for values from 0 to n-1 filled with l. If there are duplicates in l, they
    will be ignored during dequeue and only the topmost one will be used. *)
let make_fromlist n l =
   let bitmap= Array.make n false in
     List.iter (fun i -> bitmap.(i) <- true) l;
     (ref l, bitmap)

(** Dequeues an integer or raises Empty. *)
let rec dequeue (qref,bitmap) =
  match !qref with
    [] -> raise Empty
  | n::ns ->
    qref := ns;
    if bitmap.(n) then (bitmap.(n) <- false; n)
    else dequeue(qref,bitmap) (* should not happen unless made with duplicates in make_fromlist,
                                 then the duplicates are ignored and only the topmost value is
                                 used. *)

let print_queue (qref,bitmap) =
  List.iter (fun x->
    if bitmap.(x) then
     print_string ((string_of_int x)^",")
    else ())
  !qref;
  print_string "\n"

(** Enqueues an integer if it isn't in the queue yet. *)
let enqueue (qref,bitmap) n =
  if bitmap.(n)=true then ()
  else
    qref := n::!qref;
    bitmap.(n) <- true

let is_empty queue =
  try
    let n = dequeue queue in
    enqueue queue n; false
  with
    Empty -> true 

(** Iterates over the queue by dequeuing integers until it is empty. *)
let rec iter f queue =
  try
    let x = dequeue queue in
    f(x); iter f queue
  with Empty -> ()

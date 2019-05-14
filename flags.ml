let verbose_main : bool ref = ref false
let verbose_all : bool ref = ref false
let verbose_preprocessing : bool ref = ref false
let verbose_proofs : bool ref = ref false
let verbose_typing : bool ref = ref false
let verbose_queues : bool ref = ref false
let verbose_profiling : bool ref = ref false
let normalize = ref false
let normalization_depth = ref 1
let quiet : bool ref = ref false
(* 0 is infinite *)
let maxiters : int ref = ref 0
let type_format : string ref = ref "full"

let propagate_flags () : unit =
  if !verbose_all then
    begin
      verbose_main := true;
      verbose_preprocessing := true;
      verbose_proofs := true;
      verbose_typing := true;
      verbose_queues := true;
      verbose_profiling := true
    end
  else if !verbose_main then
    begin
      verbose_preprocessing := true;
      verbose_typing := true;
      verbose_queues := true;
      verbose_profiling := true
    end

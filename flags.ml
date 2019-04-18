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

let propagate_flags () : unit =
  if !verbose_all then
    begin
      verbose_preprocessing := true;
      verbose_proofs := true;
      verbose_typing := true;
      verbose_queues := true;
      verbose_profiling := true
    end

(*
let emptiness_check = ref true 
let certificate = ref false
let outputfile = ref ""
let flow = ref true
let bdd_mode = ref 0
let add_flow_cts = ref false
let profile = ref false
let report_type_env = ref true
let ce = ref true
let subty = ref false
let compute_alltypes = ref false
let subtype_hash = ref false
let nosubtype = ref false
let ty_of_term = ref false
let overwrite = ref true
let incremental = ref true
let merge_vte = ref false
let eager = ref true
*)

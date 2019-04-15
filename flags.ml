let debugging : bool ref = ref false (* TODO this should be for stuff not needed for users *)
let verbose : bool ref = ref false (* TODO this should be fore stuff intended for users, change to verbosity level *)
let normalize : bool ref = ref false
let normalization_depth : int ref = ref 1
let quiet : bool ref = ref false
let maxiters : int option ref = ref None
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

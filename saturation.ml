open Binding
open Grammar
open GrammarCommon
open HGrammar
open Profiling
open Sort
open Type
open Utilities

class saturation (hg : HGrammar.hgrammar) (cfa : Cfa.cfa) = object(self)
  (* Design note: typing with specific environments occurs in Typing, but this module is used to
     prepare precise specification of these environments based on 0CFA output, Typing does not
     use 0CFA depdendency information. *)
  
  (** Place to store result if it was computed before fixpoint. *)
  val mutable result : bool option = None

  (** Current iteration number kept for debugging purposes only. *)
  val mutable iteration : int = 0

  (** Part that stores types and types specific terms and nonterminals. *)
  val typing = new Typing.typing hg

  (* --- queues --- *)

  (* the queues below are defined in the order they are dequeued (the next one on the list is
     dequeued after the previous one is empty) *)

  (** Each element of this queue has a new typing of hterms that should be propagated.
      Subsequently dequeued typings are for the same hterms as previously, if available. *)
  val prop_hterms_ty_queue : ity TwoLayerQueue.t = TwoLayerQueue.make hg#hterms_count

  (** Each element of this queue has all new typings of a nonterminal that should be propagated
      by recomputing nonterminals that contain this nonterminal in a linear way.
      Typings are dequeued in batches, i.e., as a pair of nonterminal and all new typings. *)
  val prop_nt_ty_queue : ty BatchQueue.t = BatchQueue.make hg#nt_count

  (** Each element of this queue is a nonterminal that has a new typing that should be
      propagated by recomputing everything that contains this nonterminal in a nonlinear way.
      Enqueuing to this queue is idempotent. *)
  val prop_nt_queue = SetQueue.make hg#nt_count

  (** Each element of this queue is a specific nonterminal binding to be typed. Subsequently
      dequeued bindings are for the same nonterminal as previously, if available. *)
  val nt_binding_queue : hterms_id binding TwoLayerQueue.t = TwoLayerQueue.make hg#nt_count

  (** Each element of this queue is a nonterminal to be typed. Enqueuing to this queue is
      idempotent. *)
  val nt_queue = SetQueue.make hg#nt_count

  (** Each element of this queue is a sequence of hterms to be typed. Enqueuing to this queue
      is idempotent. *)
  val hterms_queue = SetQueue.make hg#hterms_count

  (* --- printing --- *)
  
  method print_status (is_finished : bool) =
    let title =
      if is_finished then
        "FINISHED AFTER " ^ string_of_int iteration ^ " ITERATIONS"
      else
        "ITERATION " ^ string_of_int iteration
    in
    print_string @@ "================ " ^ title ^
                    "================ \n";
    typing#print_nt_ity;
    print_string "\n";
    typing#print_hterms_hty cfa#hterms_are_arg

  (* --- typing --- *)

  (** Infers type of given hterm under given bindings. If the type is new, it is registered. *)
  (* TODO this was update_ty_of_id *)
  method infer_hterms_hty (id : hterms_id) (binding : hterms_id binding) =
    let mask = hg#id2vars id in
    let bindings = cfa#get_hterms_bindings id in
    let var_count = match hg#id2nt id with
      | Some nt -> hg#nt_arity nt
      | None -> 0
    in
    let envl = List.concat @@ List.map (typing#binding2envl var_count @@ Some mask) bindings in
    ()
    (*
    let update_ty_of_id_aux id venvs overwrite_flag = 
      let terms = Cfa.id2terms id in
      List.iter
        (fun venv -> 
           let ty = ty_of_terms venv terms in (* compute type of terms (iteration) in given environment
                                                 based on automata typings (cte) for terminals,
                                                 computed nonterminal types (nt_ity) for nonterminals,
                                                 and given environment for vars *)
           register_hterms_atys id ty overwrite_flag)
        venvs
    in
    let venvs = mk_venvs_mask env in
    update_ty_of_id_aux id venvs overwrite_flag (* generally, try to get and register an
                                                   intersection type for each term in sequence id *)
    *)

  (* --- processing queues --- *)

  (** Processes prop_hterms_ty_queue if not empty and returns if it was not empty. *)
  method process_prop_hterms_ty_queue : bool =
    false

  (** Processes prop_nt_ty_queue if not empty and returns if it was not empty. *)
  method process_prop_nt_ty_queue : bool =
    false

  (** Processes prop_nt_queue if not empty and returns if it was not empty. *)
  method process_prop_nt_queue : bool =
    false
      
  (** Processes prop_nt_binding_queue if not empty and returns if it was not empty. *)
  method process_nt_binding_queue : bool =
    false
      
  (** Processes nt_queue if not empty and returns if it was not empty. *)
  method process_nt_queue : bool =
    try
      let nt = SetQueue.dequeue nt_queue in
      (* TODO version for no environment ones *)
      let bindings = cfa#lookup_nt_bindings nt in
      if !Flags.verbose then
        print_string @@ "nt_queue: Enqueuing all " ^ string_of_int (List.length bindings) ^
                        " bindings of nonterminal " ^ string_of_int nt ^ "\n.";
      List.iter (fun binding ->
          TwoLayerQueue.enqueue nt_binding_queue nt binding
        ) bindings;
      true
    with
    | SetQueue.Empty -> false

  (** Processes hterms_queue if not empty and returns if it was not empty. *)
  method process_hterms_queue : bool =
    try
      let id = SetQueue.dequeue hterms_queue in
      if !Flags.verbose then
        print_string @@ "hterms_queue: Typing hterms " ^ string_of_int id ^ ".\n";
      cfa#get_hterms_bindings id |> List.iter (self#infer_hterms_hty id);
      true
    with
    | SetQueue.Empty -> false

  (* --- saturation main loop --- *)

  (** Performs a single iteration of the main loop. Processes a single task from one of the queues.
      Returns whether at least one of the queues was not empty. *)
  method process_queues : bool =
    if !Flags.debugging then
      self#print_status false;
    self#process_prop_hterms_ty_queue ||
    self#process_prop_nt_ty_queue ||
    self#process_prop_nt_queue ||
    self#process_nt_binding_queue ||
    self#process_nt_queue ||
    self#process_hterms_queue
  
  (** Performs saturation and returns whether the language is finite. *)
  method saturate : bool =
    profile "saturation" (fun () ->
        while self#process_queues && result = None do
          iteration <- iteration + 1
        done
      );
    if !Flags.debugging then
      self#print_status true;
    match result with
    | Some r ->
      if !Flags.debugging then
        if r then
          print_string "The input HORS contains paths with arbitrarily many counted terminals.\n"
        else
          print_string @@ "The input HORS contains only paths with uniformly bounded number " ^
                          "of counted terminals (result obtained before fixpoint).\n";
      r
    | None ->
      if !Flags.debugging then
          print_string @@ "The input HORS contains only paths with uniformly bounded number " ^
                          "of counted terminals (result obtained after fixpoint).\n";
      result <- Some false;
      false

  initializer
    (* initializing queues *)

    (* enqueueing all nonterminals that can be computed without environment *)
    (* TODO this was connected with Flags.eager condition with including nts with true
       cfa#has_head_vars nt as an optimization *)
    for nt = 0 to hg#nt_count - 1 do
      if hg#nt_arity nt = 0 then
        SetQueue.enqueue nt_queue nt
    done;
    
    (* enqueuing all hterms that are arguments to a nonterminal *)
    for id = 0 to hg#hterms_count - 1 do
      if cfa#hterms_are_arg id then
        SetQueue.enqueue hterms_queue id
    done
end

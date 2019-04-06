open Binding
open Cfa
open Grammar
open GrammarCommon
open HGrammar
open Profiling
open Sort
open TargetEnvListMap
open Type
open Utilities

class saturation (hg : HGrammar.hgrammar) (cfa : cfa) = object(self)
  (* Design note: typing with specific environments occurs in Typing, but this module is used to
     prepare precise specification of these environments based on 0CFA output, Typing does not
     use 0CFA depdendency information. *)
  
  (** Place to store result if it was computed before fixpoint. *)
  val mutable result : bool option = None

  (** Current iteration number kept for debugging purposes only. *)
  val mutable iteration : int = 0

  (** Part that stores types and types specific terms and nonterminals. *)
  val typing = new Typing.typing hg

  (** Duplication Factor graph. *)
  val dfg = new DuplicationFactorGraph.dfg

  (* --- queues --- *)

  (* the queues below are defined in the order they are dequeued (the next one on the list is
     dequeued after the previous one is empty) *)

  (** Each element of this queue has a new typing of hterms that should be propagated.
      Subsequently dequeued typings are for the same hterms as previously, if available. *)
  val prop_hterms_hty_queue : hty TwoLayerQueue.t = TwoLayerQueue.make hg#hterms_count

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

  method print_queues =
    print_string @@ "prop_hterms_hty_queue: " ^
                    TwoLayerQueue.string_of_queue string_of_hty prop_hterms_hty_queue
                    ^ "\n" ^
                    (* "prop_nt_ty_queue: " ^ BatchQueue.print_queue string_of_ty ^ "\n" ^ *)
                    "prop_nt_queue: " ^ SetQueue.string_of_queue prop_nt_queue ^ "\n" ^
                    "nt_binding_queue: " ^
                    TwoLayerQueue.string_of_queue (string_of_binding string_of_int)
                      nt_binding_queue ^
                    "\n" ^
                    "nt_queue: " ^ SetQueue.string_of_queue nt_queue ^ "\n" ^
                    "hterms_queue: " ^ SetQueue.string_of_queue hterms_queue ^ "\n"
  
  method print_status (is_finished : bool) =
    let title =
      if is_finished then
        "FINISHED AFTER " ^ string_of_int iteration ^ " ITERATIONS"
      else
        "ITERATION " ^ string_of_int iteration
    in
    print_string @@ "\n================ " ^ title ^
                    " ================ \n";
    typing#print_nt_ity;
    print_string "\n";
    typing#print_hterms_hty cfa#hterms_are_arg;
    self#print_queues;
    print_string "\n"

  (* --- processing results of typing --- *)

  method register_nt_ty (nt : nt_id) (ty : ty) (used_nts : nt_tys) (positive : bool) =
    if typing#add_nt_ty nt ty then
      begin
        if !Flags.verbose then
          print_string @@ "Registering new typing of nonterminal " ^ string_of_int nt ^ " : " ^
                          string_of_ty ty ^ "\n";
        (* adding the new typing to the graph and checking for positive cycle *)
        dfg#add_vertex nt ty used_nts positive;
        if dfg#has_positive_cycle hg#start_nt PR then
          result <- Some true;
        SetQueue.enqueue prop_nt_queue nt
      end
  
  method register_hterms_hty (id : hterms_id) (hty : hty) =
    (* TODO subtyping and overwriting logic *)
    if typing#add_hterms_hty id hty then
      begin
        if !Flags.verbose then
          print_string @@ "Registering new typing of hterms " ^ string_of_int id ^ " : " ^
                          string_of_hty hty ^ "\n";
        TwoLayerQueue.enqueue prop_hterms_hty_queue id hty
      end

  (* --- typing --- *)

  method infer_nt_ity (nt : nt_id) (fixed_hterms_hty : (hterms_id * hty) option)
      (binding : hterms_id binding) =
    if !Flags.verbose then
      begin
        print_string @@ "* Inferring type of nonterminal " ^ string_of_int nt ^ " under binding " ^
                        string_of_binding string_of_int binding ^ " and ";
        match fixed_hterms_hty with
        | Some (id, hty) ->
          print_string @@ "fixed typing of hterms " ^ string_of_int id ^ " to " ^
                          string_of_hty hty ^ ".\n"
        | None ->
          print_string "no fixed typings.\n"
      end;
    let body = hg#nt_body nt in
    let var_count = hg#nt_arity nt in
    let envl = typing#binding2envl var_count None fixed_hterms_hty binding in
    EnvList.iter (fun envm ->
        let tel = typing#type_check body None (Left envm.env) false false in
        tel |> TargetEnvl.iter_fun_ty (fun ty used_nts positive ->
            self#register_nt_ty nt ty used_nts positive
          )
      ) envl
  
  (** Infers type of given hterm under given bindings. If the type is new, it is registered. *)
  method infer_hterms_hty (id : hterms_id) (fixed_hterms_hty : (hterms_id * hty) option)
      (binding : hterms_id binding) =
    if !Flags.verbose then
      begin
        print_string @@ "* Inferring type of hterms " ^ string_of_int id ^ " under binding " ^
                        string_of_binding string_of_int binding ^ " and ";
        match fixed_hterms_hty with
        | Some (id, hty) ->
          print_string @@ "fixed typing of hterms " ^ string_of_int id ^ " to " ^
                          string_of_hty hty ^ ".\n"
        | None ->
          print_string "no fixed typings.\n"
      end;
    let mask = hg#id2vars id in
    let var_count = match hg#id2nt id with
      | Some nt -> hg#nt_arity nt
      | None -> 0
    in
    let hterms = hg#id2hterms id in
    let envl = typing#binding2envl var_count (Some mask) None binding in
    envl |> EnvList.iter (fun envm ->
        let tels = hterms |> List.map (fun hterm ->
            typing#type_check hterm None (Left envm.env) false false
          )
        in
        let hty = tels |> List.map TargetEnvl.targets in
        self#register_hterms_hty id hty
      )

  (* --- processing queues --- *)

  (** Processes prop_hterms_hty_queue if not empty and returns if it was not empty. *)
  method process_prop_hterms_hty_queue : bool =
    try
      let id, hty = TwoLayerQueue.dequeue prop_hterms_hty_queue in
      if !Flags.verbose then
        print_string @@ "prop_nt_queue: Propagating new types of hterms " ^
                        string_of_int id ^ " : " ^ string_of_hty hty ^ ".\n";
      (* This step is required, because new typing of hterms might be enough to type other hterms,
         but not enough to type a whole nonterminal if it needs typings of more hterms. And these
         newly typed hterms may be enough to type some nonterminal, while it would be impossible
         without their new typing. *)
      cfa#get_hterms_where_hterms_flow id |> SortedHTermsIds.iter (fun id' ->
          cfa#get_hterms_bindings id' |>
          (* TODO this should be pre-filtered in cfa, like for nt *)
          List.filter (List.exists (fun (_, _, id'') -> id'' = id)) |>
          List.iter @@ self#infer_hterms_hty id' (Some (id, hty))
        );
      (* This step is required, because when a new type is computed for hterms,
         nonterminals are typed with new possible typings of arguments, which may generate
         new nonterminal typings. *)
      cfa#get_nt_bindings_applied_to_hterms id |> List.iter (fun (nt, binding) ->
          self#infer_nt_ity nt (Some (id, hty)) binding
        );
      true
    with
    | TwoLayerQueue.Empty -> false

  (** Processes prop_nt_ty_queue if not empty and returns if it was not empty. *)
  method process_prop_nt_ty_queue : bool =
    (* TODO this is to be implemented when implementing special case for linear nonterminals *)
    false

  (** Processes prop_nt_queue if not empty and returns if it was not empty. *)
  method process_prop_nt_queue : bool =
    try
      let nt = SetQueue.dequeue prop_nt_queue in
      if !Flags.verbose then
        print_string @@ "prop_nt_queue: Propagating all types of nonterminal " ^
                        string_of_int nt ^ ".\n";
      (* This step is required, because when a new type is computed for a nonterminal, type of
         application of this nonterminal to other terms may yield new possible typings and
         effectively give new type for the terms it is contained in. *)
      cfa#get_nt_containing_nt nt |> SortedNTs.iter (fun nt' ->
          SetQueue.enqueue nt_queue nt';
          (* removing bindings for that nt, since all of its bindings will be recomputed *)
          TwoLayerQueue.remove_all nt_binding_queue nt'
        );
      (* This step is required, because when a new type is computed for a nonterminal, new typings
         of hterms that contain it may be computed. *)
      cfa#get_hterms_containing_nt nt |> SortedHTermsIds.iter (fun id ->
          SetQueue.enqueue hterms_queue id
        );
      true
    with
    | SetQueue.Empty -> false
      
  (** Processes prop_nt_binding_queue if not empty and returns if it was not empty. *)
  method process_nt_binding_queue : bool =
    try
      let nt, binding = TwoLayerQueue.dequeue nt_binding_queue in
      if !Flags.verbose then
        print_string @@ "nt_binding_queue: Typing nonterminal " ^ string_of_int nt ^
                        " with binding " ^ string_of_binding string_of_int binding ^ ".\n";
      self#infer_nt_ity nt None binding;
      true
    with
    | TwoLayerQueue.Empty -> false

  (** Processes nt_queue if not empty and returns if it was not empty.
      It finds all bindings of a nonterminal and enqueues them to be typed. *)
  method process_nt_queue : bool =
    try
      let nt = SetQueue.dequeue nt_queue in
      (* TODO version for no environment ones *)
      let bindings = cfa#lookup_nt_bindings nt in
      if !Flags.verbose then
        print_string @@ "nt_queue: Enqueuing all " ^ string_of_int (List.length bindings) ^
                        " bindings of nonterminal " ^ string_of_int nt ^ ".\n";
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
      let bindings = cfa#get_hterms_bindings id in
      if !Flags.verbose then
        print_string @@ "hterms_queue: Typing hterms " ^ string_of_int id ^ " with " ^
                        string_of_int (List.length bindings) ^ " bindings.\n";
      bindings |> List.iter @@ self#infer_hterms_hty id None;
      true
    with
    | SetQueue.Empty -> false

  (* --- saturation main loop --- *)

  (** Performs a single iteration of the main loop. Processes a single task from one of the queues.
      Returns whether at least one of the queues was not empty. *)
  method process_queues : bool =
    if !Flags.debugging then
      self#print_status false;
    self#process_prop_hterms_hty_queue ||
    self#process_prop_nt_ty_queue ||
    self#process_prop_nt_queue ||
    self#process_nt_binding_queue ||
    self#process_nt_queue ||
    self#process_hterms_queue
  
  (** Performs saturation and returns whether the language is finite. *)
  method saturate : bool =
    while self#process_queues && result = None do
      iteration <- iteration + 1
    done;
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

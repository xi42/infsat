open Binding
open Cfa
open Grammar
open GrammarCommon
open HGrammar
open Profiling
open Proof
open Sort
open TargetEnvms
open Type
open TypingCommon
open Utilities

type infsat_result = Infinite | Finite | Unknown

let string_of_infsat_result = function
  | Infinite -> "infinite"
  | Finite -> "finite"
  | Unknown -> "unknown"

exception Max_iterations_reached

exception Positive_cycle_found of cycle_proof

class saturation (hg : HGrammar.hgrammar) (cfa : cfa) = object(self)
  (* Design note: typing with specific environments occurs in Typing, but this module is used to
     prepare precise specification of these environments based on 0CFA output, Typing does not
     use 0CFA depdendency information. *)

  (** Current iteration number kept for debugging purposes only. *)
  val mutable iteration : int = 1

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

  method string_of_queues =
    "prop_hterms_hty_queue: " ^
    TwoLayerQueue.string_of_queue string_of_hty prop_hterms_hty_queue
    ^ "\n" ^
    (* "prop_nt_ty_queue: " ^ BatchQueue.print_queue string_of_ty ^ "\n" ^ *)
    "prop_nt_queue: " ^ SetQueue.string_of_queue prop_nt_queue ^ "\n" ^
    "nt_binding_queue: " ^
    TwoLayerQueue.string_of_queue (string_of_binding string_of_int)
      nt_binding_queue ^
    "\n" ^
    "nt_queue: " ^ SetQueue.string_of_queue nt_queue ^ "\n" ^
    "hterms_queue: " ^ SetQueue.string_of_queue hterms_queue

  method status : string =
    "\n================ ITERATION " ^ string_of_int iteration ^
    " ================\n" ^
    typing#string_of_nt_ity ^ "\n\n" ^
    typing#string_of_hterms_hty cfa#hterms_are_arg ^ "\n\n" ^
    self#string_of_queues ^ "\n\n" ^
    "Duplication Factor Graph:\n" ^ dfg#to_string hg#nt_name

  (* --- processing results of typing --- *)

  method register_nt_ty (nt : nt_id) (ty : ty) (envm : envm) =
    if typing#add_nt_ty nt ty then
      begin
        print_verbose !Flags.verbose_typing @@ lazy (
          "Registering new typing of nonterminal " ^ hg#nt_name nt ^ " : " ^
          string_of_ty ty ^ "."
        );
        SetQueue.enqueue prop_nt_queue nt
      end;
    let proof = {
      derived = (nt, ty);
      var_assumptions = envm.env#get_var_itys;
      nt_assumptions = envm.used_nts;
      t_assumptions = envm.used_ts;
      positive = envm.positive;
      initial = false
    } in
    (* Adding the new typing to the graph and checking for positive cycle. This should
       be performed even if the typing is not new, since set of used nonterminals may be new. *)
    if dfg#add_vertex proof then
      begin
        print_verbose !Flags.verbose_typing @@ lazy (
          "The duplication factor graph was updated by adding or modifying " ^
          "an edge. Proof for added edges " ^
          "(+ - positive duplication factor/multiple uses):\n" ^
          string_of_proof hg None proof
        );
        match dfg#find_positive_cycle hg#start_nt ty_pr with
        | Some path -> raise_notrace @@ Positive_cycle_found path
        | None -> ()
      end
    else
      print_verbose !Flags.verbose_proofs @@ lazy (
        "The duplicaton factor graph was not modified. Discarded proof " ^
        "(+ - positive duplication factor/multiple uses):\n" ^
        string_of_proof hg None proof
      )

  method register_hterms_hty (id : hterms_id) (hty : hty) =
    (* TODO subtyping and overwriting logic *)
    if typing#add_hterms_hty id hty then
      begin
        print_verbose !Flags.verbose_typing @@ lazy (
          "Registering new typing of hterms " ^ string_of_int id ^ ": " ^
          hg#string_of_hterms HlocMap.empty id ^ " : " ^
          string_of_hty hty
        );
        TwoLayerQueue.enqueue prop_hterms_hty_queue id hty
      end

  (* --- typing --- *)

  method infer_nt_ity (nt : nt_id) (fixed_hterms_hty : (hterms_id * hty) option)
      (binding : hterms_id binding) =
    print_verbose !Flags.verbose_queues @@ lazy (
      let typings_info =
        match fixed_hterms_hty with
        | Some (id, hty) ->
          "fixed typing of hterms " ^ string_of_int id ^ " to " ^
          string_of_hty hty
        | None ->
          "no fixed typings"
      in
      "* Inferring type of nonterminal " ^ hg#nt_name nt ^ " under binding " ^
      string_of_binding string_of_int binding ^ " and " ^ typings_info ^ "."
    );
    indent (+1);
    let body = hg#nt_body nt in
    let var_count = hg#nt_arity nt in
    let envms = typing#binding2envms var_count None fixed_hterms_hty binding in
    envms |> Envms.iter (fun envm ->
        let tel = typing#type_check body None (Left envm.env) false false 0 in
        tel |> TargetEnvms.iter_fun_ty (fun ty envm ->
            self#register_nt_ty nt ty envm
          )
      );
    indent (-1)
  
  (** Infers type of given hterm under given bindings. If the type is new, it is registered. *)
  method infer_hterms_hty (id : hterms_id) (fixed_hterms_hty : (hterms_id * hty) option)
      (binding : hterms_id binding) =
    print_verbose !Flags.verbose_queues @@ lazy (
      let typing_info =
        match fixed_hterms_hty with
        | Some (id, hty) ->
          "fixed typing of hterms " ^ string_of_int id ^ " to " ^
          string_of_hty hty
        | None ->
          "no fixed typings"
      in
      "* Inferring type of hterms " ^ string_of_int id ^ " under binding " ^
      string_of_binding string_of_int binding ^ " and " ^ typing_info ^ "."
    );
    indent (+1);
    let mask = hg#id2vars id in
    let var_count = match hg#id2nt id with
      | Some nt -> hg#nt_arity nt
      | None -> 0
    in
    let hterms = hg#id2hterms id in
    let envms = typing#binding2envms var_count (Some mask) None binding in
    envms |> Envms.iter (fun envm ->
        let tels = hterms |> List.map (fun hterm ->
            typing#type_check hterm None (Left envm.env) false false 0
          )
        in
        let hty = tels |> List.map TargetEnvms.targets_as_args in
        self#register_hterms_hty id hty
      );
    indent (-1)

  (* --- processing queues --- *)

  (** Processes prop_hterms_hty_queue if not empty and returns if it was not empty. *)
  method process_prop_hterms_hty_queue : bool =
    try
      let id, hty = TwoLayerQueue.dequeue prop_hterms_hty_queue in
      print_verbose !Flags.verbose_queues @@ lazy (
        "prop_nt_queue: Propagating new types of hterms " ^
        string_of_int id ^ " : " ^ string_of_hty hty ^ "."
      );
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
      print_verbose !Flags.verbose_queues @@ lazy (
        "prop_nt_queue: Propagating all types of nonterminal " ^
        hg#nt_name nt ^ "."
      );
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
      print_verbose !Flags.verbose_queues @@ lazy (
        "nt_binding_queue: Typing nonterminal " ^ hg#nt_name nt ^
        " with binding " ^ string_of_binding string_of_int binding ^ "."
      );
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
      print_verbose !Flags.verbose_queues @@ lazy (
        "nt_queue: Enqueuing all " ^ string_of_int (List.length bindings) ^
        " bindings of nonterminal " ^ hg#nt_name nt ^ "."
      );
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
      print_verbose !Flags.verbose_queues @@ lazy (
        "hterms_queue: Typing hterms " ^ string_of_int id ^ " with " ^
        string_of_int (List.length bindings) ^ " bindings.";
      );
      bindings |> List.iter @@ self#infer_hterms_hty id None;
      true
    with
    | SetQueue.Empty -> false

  (* --- saturation main loop --- *)

  (** Performs a single iteration of the main loop. Processes a single task from one of the queues.
      Returns whether at least one of the queues was not empty. *)
  method process_queues : bool =
    print_verbose !Flags.verbose_queues @@ lazy self#status;
    self#process_prop_hterms_hty_queue ||
    self#process_prop_nt_ty_queue ||
    self#process_prop_nt_queue ||
    self#process_nt_binding_queue ||
    self#process_nt_queue ||
    self#process_hterms_queue
  
  (** Performs saturation and returns whether the language is finite. *)
  method saturate : infsat_result =
    try
      while self#process_queues do
        if iteration = !Flags.maxiters then
          raise_notrace Max_iterations_reached;
        iteration <- iteration + 1
      done;
      print_verbose (not !Flags.quiet) @@ lazy (
        "Duplication Factor Graph:\n" ^ dfg#to_string hg#nt_name ^ "\n" ^
        "Computed result after " ^ string_of_int iteration ^ " iterations.\n" ^
        "The input HORS contains only paths with uniformly bounded number " ^
        "of counted terminals.";
      );
      Finite
    with
    | Positive_cycle_found cycle_path ->
      reset_indentation ();
      print_verbose (not !Flags.quiet) @@ lazy (
        "Duplication Factor Graph:\n" ^
        dfg#to_string hg#nt_name ^ "\n" ^
        "Computed result after " ^ string_of_int iteration ^ " iterations.\n" ^
        "The input HORS contains paths with arbitrarily many counted terminals.\n" ^
        cycle_path#to_string hg
      );
      Infinite
    | Max_iterations_reached ->
      print_verbose (not !Flags.quiet) @@ lazy (
        "Could not determine the result in " ^ string_of_int iteration ^ " iterations."
      );
      Unknown

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

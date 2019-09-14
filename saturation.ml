open Binding
open Cfa
open Environment
open Grammar
open GrammarCommon
open HGrammar
open Profiling
open Proof
open TargetEnvs
open Type
open TypingCommon
open Utilities

type infsat_result = Infinite of string | Finite | Unknown

let string_of_infsat_result = function
  | Infinite _ -> "infinite"
  | Finite -> "finite"
  | Unknown -> "unknown"

exception Max_iterations_reached

exception Positive_cycle_found of cycle_proof

class saturation (hg : HGrammar.hgrammar) (cfa : cfa) = object(self)
  (* Design note: typing with specific environments occurs in Typing. This module is used to
     prepare precise specification of these environments based on 0CFA output. Typing does not
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

  (** Each element of this queue is a new typing of a nonterminal that should be propagated
      by recomputing nonterminals and hterms that contain this nonterminal.
      Typings are dequeued in batches, i.e., as a pair of nonterminal and all new typings.
      If no_force_nt_ty_opt is on then the types are ignored and the new type of nonterminal
      is not forced. *)
  val prop_nt_ty_queue : ty BatchQueue.t = BatchQueue.make hg#nt_count

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
    "prop_nt_ty_queue: " ^ BatchQueue.string_of_queue string_of_ty prop_nt_ty_queue ^ "\n" ^
    "nt_queue: " ^ SetQueue.string_of_queue nt_queue ^ "\n" ^
    "hterms_queue: " ^ SetQueue.string_of_queue hterms_queue

  method status : string =
    "\n================ ITERATION " ^ string_of_int iteration ^
    " ================\n" ^
    typing#string_of_nt_ity ^ "\n\n" ^
    typing#string_of_hterms_hty cfa#hterms_are_arg ^ "\n\n" ^
    self#string_of_queues ^ "\n\n" ^
    "Duplication Factor Graph:\n" ^ dfg#to_string hg#nt_name

  method iter_counter : string =
    "Starting iteration " ^ string_of_int iteration ^ "."

  (* --- processing results of typing --- *)

  method register_nt_ty (nt : nt_id) (ty : ty) (env : env) =
    if typing#add_nt_ty nt ty then
      begin
        print_verbose !Flags.verbose_typing @@ lazy (
          "Registering new typing of nonterminal " ^ hg#nt_name nt ^ " : " ^
          string_of_ty ty ^ "."
        );
        BatchQueue.enqueue prop_nt_ty_queue nt ty
      end;
    let proof = {
      derived = (nt, ty);
      used_nts = env.used_nts;
      loc_types = env.loc_types;
      positive = env.positive;
      initial = false
    } in
    (* Adding the new typing to the graph and checking for positive cycle. This should
       be performed even if the typing is not new, since set of used nonterminals may be new. *)
    if dfg#add_vertex proof then
      begin
        print_verbose !Flags.verbose_typing @@ lazy (
          "The duplication factor graph was updated by adding or modifying " ^
          "an edge. Proof for added edges " ^
          "(+ - positive duplication factor):\n" ^
          string_of_proof hg None proof
        );
        match dfg#find_positive_cycle hg#start_nt ty_pr with
        | Some path -> raise_notrace @@ Positive_cycle_found path
        | None -> ()
      end
    else
      print_verbose !Flags.verbose_proofs @@ lazy (
        "No edge was added or modified in the duplicaton factor graph. The proof was " ^
        "(+ - positive duplication factor/multiple uses):\n" ^
        string_of_proof hg None proof
      )

  method register_hterms_hty (id : hterms_id) (hty : hty) =
    (* TODO subtyping and overwriting logic *)
    if typing#add_hterms_hty id hty then
      begin
        print_verbose !Flags.verbose_typing @@ lazy (
          "Registering new typing of hterms " ^ hg#string_of_hterms id ^ ": " ^
          hg#string_of_hterms id ^ " : " ^
          string_of_hty hty
        );
        TwoLayerQueue.enqueue prop_hterms_hty_queue id hty
      end

  (* --- typing --- *)

  (** Infers types of given nonterminal. Has an option to force types of some hterms.
      Works by generating a list of all possible environments based on bindings and then iterating
      over it while typing the nonterminal. *)
  method infer_nt_ty (nt : nt_id) (forced_hterms_hty : (hterms_id * hty) option)
      (forced_nt_ity : (nt_id * TySet.t) option) (binding : hterms_id binding option) =
    print_verbose !Flags.verbose_queues @@ lazy (
      let binding_info =
        match binding with
        | Some binding ->
          " under binding " ^ string_of_binding string_of_int binding ^ " and"
        | None -> ""
      in
      let forced_hterms_hty_str =
        match forced_hterms_hty with
        | Some (id, hty) ->
          " forced typing of hterms " ^ string_of_int id ^ " " ^ hg#string_of_hterms id ^
          " : " ^ string_of_hty hty
        | None ->
          ""
      in
      let forced_nt_ity_str =
        match forced_nt_ity with
        | Some (nt, ity) ->
          " forced typing of nonterminal " ^ hg#nt_name nt ^
          " : " ^ concat_map " \\/ " string_of_ty (TySet.elements ity)
        | None ->
          ""
      in
      "* Inferring type of nonterminal " ^ hg#nt_name nt ^ binding_info ^
      forced_hterms_hty_str ^ forced_nt_ity_str ^ "."
    );
    indent (+1);
    let body = hg#nt_body nt in
    let te =
      match binding with
      | Some binding ->
        let ctx = typing#binding2ctx body None forced_hterms_hty None binding in
        typing#type_check body None ctx false false
      | None ->
        assert (forced_hterms_hty = None);
        assert (forced_nt_ity = None);
        typing#type_check body None Context.empty_ctx false false
    in
    te |> TargetEnvs.iter_fun_ty (hg#nt_arity nt) (fun ty env ->
        self#register_nt_ty nt ty env
      );
    indent (-1)
  
  (** Infers type of given hterm under given bindings. If the type is new, it is registered.
      Has an option to force types of some hterms.
      Works by generating a list of all possible environments based on bindings and then iterating
      over it while typing the nonterminal. *)
  method infer_hterms_hty (id : hterms_id) (forced_hterms_hty : (hterms_id * hty) option)
      (forced_nt_ity : (nt_id * TySet.t) option) (binding : hterms_id binding) =
    print_verbose !Flags.verbose_queues @@ lazy (
      let typing_info =
        match forced_hterms_hty with
        | Some (id, hty) ->
          "forced typing of hterms " ^ hg#string_of_hterms id ^ " " ^
          hg#string_of_hterms id ^ " to " ^ string_of_hty hty
        | None ->
          "no forced typings"
      in
      let hterms_str =
        hg#string_of_hterms id
      in
      "* Inferring type of hterms " ^ hterms_str ^ " under binding " ^
      string_of_binding string_of_int binding ^ " and " ^ typing_info ^ "."
    );
    indent (+1);
    let mask = hg#id2vars id in
    let hterms = hg#id2hterms id in
    let tes = hterms |> List.map (fun hterm ->
        let ctx = typing#binding2ctx hterm (Some mask) forced_hterms_hty None binding in
        typing#type_check hterm None ctx false false
      )
    in
    let hty =
      Array.of_list @@
      List.map (fun te -> TySet.of_ity @@ TargetEnvs.targets_as_args te) @@
      tes
    in
    self#register_hterms_hty id hty;
    indent (-1)

  (* --- processing queues --- *)

  (** Processes prop_hterms_hty_queue if not empty and returns if it was not empty. *)
  method process_prop_hterms_hty_queue : bool =
    try
      let id, hty = TwoLayerQueue.dequeue prop_hterms_hty_queue in
      print_verbose !Flags.verbose_queues @@ lazy (
        "prop_nt_queue: Propagating new types of hterms " ^
        hg#string_of_hterms id ^ " : " ^ string_of_hty hty ^ "."
      );
      (* This step is required, because new typing of hterms might be enough to type other hterms,
         but not enough to type a whole nonterminal if it needs typings of more hterms. And these
         newly typed hterms may be enough to type some nonterminal, while it would be impossible
         without their new typing. *)
      cfa#get_hterms_where_hterms_flow id |> SortedHTermsIds.iter (fun recomputed_id ->
          if !Flags.no_force_hterms_hty_opt then
            SetQueue.enqueue hterms_queue recomputed_id
          else
            (* sort_and_delete_duplicates is here to not repeat the work when the same
               binding is present twice (a rare occurence). This will break if these bindings
               stop being tuples of ints due to default compare. *)
            cfa#get_hterms_bindings recomputed_id |>
            sort_and_delete_duplicates |>
            List.filter (List.exists (fun (_, _, id'') -> id'' = id)) |>
            List.iter @@ self#infer_hterms_hty recomputed_id (Some (id, hty)) None
        );
      (* This step is required, because when a new type is computed for hterms,
         nonterminals are typed with new possible typings of arguments, which may generate
         new nonterminal typings. *)
      cfa#get_nt_bindings_applied_to_hterms id |> List.iter (fun (nt, binding) ->
          self#infer_nt_ty nt (Some (id, hty)) None @@ Some binding
        );
      true
    with
    | TwoLayerQueue.Empty -> false

  (** Processes prop_nt_ty_queue if not empty and returns if it was not empty. *)
  method process_prop_nt_ty_queue : bool =
    try
      let nt, tys = BatchQueue.dequeue prop_nt_ty_queue in
      if !Flags.no_force_nt_ty_opt then
        begin
          print_verbose !Flags.verbose_queues @@ lazy (
            "prop_nt_queue: Propagating all types of nonterminal " ^
            hg#nt_name nt ^ "."
          );
          (* This step is required, because when a new type is computed for a nonterminal, type
             of application of this nonterminal to other terms may yield new possible typings
             and effectively give new type for the terms it is contained in. *)
          cfa#get_nt_containing_nt nt |> SortedNTs.iter (fun nt' ->
              SetQueue.enqueue nt_queue nt'
            );
          (* This step is required, because when a new type is computed for a nonterminal, new
             typings of hterms that contain it may be computed. *)
          cfa#get_hterms_containing_nt nt |> SortedHTermsIds.iter (fun id ->
              SetQueue.enqueue hterms_queue id
            )
        end
      else
        begin
          print_verbose !Flags.verbose_queues @@ lazy (
            "prop_nt_queue: Propagating new types of nonterminal " ^
            hg#nt_name nt ^ " : " ^ string_of_ity (TyList.of_list tys) ^ "."
          );
          let ftys = TySet.of_list tys in
          (* Inferring type of nonterminals that contain this one while enforcing usage of
             new types. *)
          cfa#get_nt_containing_nt nt |> SortedNTs.iter (fun recomputed_nt ->
              cfa#lookup_nt_bindings recomputed_nt |>
              List.map (fun binding -> Some binding) |>
              List.iter @@ self#infer_nt_ty recomputed_nt None (Some (nt, ftys))
            );
          (* Inferring type of hterms that contain this nonterminal while enforcing usage of
             new types. *)
          cfa#get_hterms_containing_nt nt |> SortedHTermsIds.iter (fun recomputed_id ->
              cfa#get_hterms_bindings recomputed_id |>
              sort_and_delete_duplicates |>
              List.iter @@ self#infer_hterms_hty recomputed_id None (Some (nt, ftys))
            );
        end;
      true
    with
    | BatchQueue.Empty -> false

  (** Processes nt_queue if not empty and returns if it was not empty.
      It finds all bindings of a nonterminal and enqueues them to be typed. *)
  method process_nt_queue : bool =
    try
      let nt = SetQueue.dequeue nt_queue in
      if !Flags.no_headvar_opt || cfa#nt_has_headvars nt then
        let bindings = cfa#lookup_nt_bindings nt in
        print_verbose !Flags.verbose_queues @@ lazy (
          "nt_queue: Typing all " ^ string_of_int (List.length bindings) ^
          " bindings of nonterminal " ^ hg#nt_name nt ^ "."
        );
        List.iter (fun binding ->
            print_verbose !Flags.verbose_typing @@ lazy (
              "* Typing nonterminal " ^ hg#nt_name nt ^
              " with binding " ^ string_of_binding string_of_int binding ^ "."
            );
            indent (+1);
            self#infer_nt_ty nt None None @@ Some binding;
            indent (-1)
          ) bindings
      else
        begin
          print_verbose !Flags.verbose_queues @@ lazy (
            "nt_queue: Typing head variable-free nonterminal " ^ hg#nt_name nt ^ "."
          );
          self#infer_nt_ty nt None None None
        end;
      true
    with
    | SetQueue.Empty -> false

  (** Processes hterms_queue if not empty and returns if it was not empty. *)
  method process_hterms_queue : bool =
    try
      let id = SetQueue.dequeue hterms_queue in
      let bindings = cfa#get_hterms_bindings id in
      print_verbose !Flags.verbose_queues @@ lazy (
        "hterms_queue: Typing hterms " ^ hg#string_of_hterms id ^ " with " ^
        string_of_int (List.length bindings) ^ " bindings.";
      );
      bindings |> sort_and_delete_duplicates |>
      List.iter @@ self#infer_hterms_hty id None None;
      true
    with
    | SetQueue.Empty -> false

  (* --- saturation main loop --- *)

  (** Performs a single iteration of the main loop. Processes a single task from one of the queues.
      Returns whether at least one of the queues was not empty. *)
  method process_queues : bool =
    print_verbose !Flags.verbose_queues @@ lazy self#status;
    print_verbose (!Flags.verbose_iters && not !Flags.verbose_queues) @@ lazy self#iter_counter;
    self#process_prop_hterms_hty_queue ||
    self#process_prop_nt_ty_queue ||
    self#process_nt_queue ||
    self#process_hterms_queue
  
  (** Performs saturation and returns whether the language is finite. Takes optional safety error
      message if the term is unsafe. When flag force_unsafe is false (default) and the output
      is finite language, it returns Unknown with appropriate message instead. *)
  method saturate (safety_error : string option) : infsat_result =
    let start_t = Sys.time () in
    try
      while self#process_queues do
        if iteration = !Flags.maxiters then
          raise_notrace Max_iterations_reached;
        iteration <- iteration + 1
      done;
      let t = Sys.time () -. start_t in
      print_verbose (not !Flags.quiet) @@ lazy (
        "Duplication Factor Graph:\n" ^ dfg#to_string hg#nt_name ^ "\n" ^
        "Computed saturation result after " ^ string_of_int iteration ^ " iterations in " ^
        string_of_float t ^ "s.\n" ^
        "The input HORS contains only paths with uniformly bounded number " ^
        "of counted terminals.";
      );
      match !Flags.force_unsafe, safety_error with
      | false, Some error ->
        print_verbose (not !Flags.quiet) @@ lazy (
          "\nHowever, one of the terms is unsafe:\n" ^
          error ^ "\n\n" ^
          "The correctness of this output depends on an unproven hypothesis that the type " ^
          "system used in this work is correct for all term. If you wish to assume that this " ^
          "hypothesis holds, use -f option."
        );
        Unknown
      | _, _ -> Finite
    with
    | Positive_cycle_found cycle_proof ->
      let t = Sys.time () -. start_t in
      reset_indentation ();
      let cycle_proof_str = cycle_proof#to_string hg in
      print_verbose (not !Flags.quiet) @@ lazy (
        "Duplication Factor Graph:\n" ^
        dfg#to_string hg#nt_name ^ "\n" ^
        cycle_proof_str ^ "\n\n" ^
        "Computed saturation result after " ^ string_of_int iteration ^ " iterations in " ^
        string_of_float t ^ "s.\n" ^
        "The input HORS contains paths with arbitrarily many counted terminals."
      );
      Infinite cycle_proof_str
    | Max_iterations_reached ->
      let t = Sys.time () -. start_t in
      print_verbose (not !Flags.quiet) @@ lazy (
        "Could not determine saturation result in " ^ string_of_int iteration ^
        " iterations in " ^ string_of_float t ^ "s.\n."
      );
      Unknown

  initializer
    (* initializing queues *)

    (* enqueueing all nonterminals that can be computed without environment *)
    for nt = 0 to hg#nt_count - 1 do
      if hg#nt_arity nt = 0 || not !Flags.no_headvar_opt && not @@ cfa#nt_has_headvars nt then
        SetQueue.enqueue nt_queue nt
    done;
    
    (* enqueuing all hterms that are arguments to a nonterminal *)
    for id = 0 to hg#hterms_count - 1 do
      if cfa#hterms_are_arg id then
        SetQueue.enqueue hterms_queue id
    done
end

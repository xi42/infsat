open GrammarCommon
open Grammar
open Utilities

type midhead = MT of terminal | MNT of string | MVar of string | MFun of string list * midterm
and midterm = MApp of midhead * midterm list
type midrule = string * string list * midterm
type midrules = midrule list

let nt_kinds = ref (Array.make 0 ("", O))
let ntid = ref 0
let new_nt () =
  let x = !ntid in
  ntid := x + 1;
  x

let ntauxid = ref 0
let new_ntaux () =
  let x = !ntauxid in
  ntauxid := x + 1;
  x

(** Maps nonterminal names to fresh ids. *)
let tab_nt_name2id = Hashtbl.create 1000

let register_nt ntname =
  if Hashtbl.mem tab_nt_name2id ntname then
    failwith @@ "Duplicated nonterminal " ^ ntname
  else 
    let nt = new_nt() in 
    Hashtbl.add tab_nt_name2id ntname nt;
    (!nt_kinds).(nt) <- (ntname, O) (* for the moment, ignore the kind *)

let lookup_nt_id nt_name =
  try Hashtbl.find tab_nt_name2id nt_name
  with Not_found -> failwith @@ "Undefined nonterminal " ^ nt_name

let aux_rules = ref []
let register_new_rule f arity body =
   aux_rules := (f, arity, body) :: !aux_rules

let rec depth_of_term term =
  match term with
  | T _ | NT _ | Var _ -> 0
  | App (t1, t2) -> max (depth_of_term t1) (depth_of_term t2 + 1)

let rec midterm2term vmap pterm =
  match pterm with
  | MApp (h, pterms) ->
    let h' = 
      match h with
      | MVar s ->
        begin
          try
            Var (List.assoc s vmap)
          with
          | Not_found -> failwith @@ "Undefined variable " ^ s ^ " used"
        end
      | MNT s -> NT (lookup_nt_id s)
      | MFun _ -> failwith "Expected no functions at this point"
      | MT a -> T a
    in
    let terms = List.map (midterm2term vmap) pterms in
    let terms' = if !Flags.normalize then
        List.map normalize_term terms
      else
        terms
    in
    mk_app h' terms'

and normalize_term term =
  match term with
  | App _ -> (* reduces outer applications *)
    if depth_of_term term > !Flags.normalization_depth then
      let vars = SortedVars.to_list @@ vars_in_term term in
      let arity = List.length vars in
      let nt = new_ntaux () in
      let subst = List.combine vars
          (List.map (fun i-> Var (nt, i)) (fromto 0 arity))
      in
      let term' = Grammar.subst_term subst term in
      register_new_rule nt arity term';
      mk_app (NT nt) (List.map (fun i -> Var i) vars)
    else
      term
  | _ -> term

let dummy_vname = "dummy_var"
let dummy_term = NT 0
let dummy_ntname = "DummyNT"

let midrule2rule rules vinfo (f, (_, ss, pterm)) =
  let ss' = index_list ss in
  let arity = List.length ss in
  let vmap = List.map (fun (i, v) -> (v, (f, i))) ss' in (* [(arg name, (nonterm ix, arg ix)) *)
  vinfo.(f) <- Array.make arity dummy_vname;
  List.iter (fun (i,v) -> (vinfo.(f).(i) <- v)) ss'; (* vinfo[nonterm id][arg ix] = arg name *)
  let term = midterm2term vmap pterm in
  rules.(f) <- (arity, term) (* F x_1 .. x_n = t => rules[F] = (n, potentially normalized term with names changed either to var or to terminal) *)

let midrules2rules rules vinfo (midrules : midrules) =
  let midrules_indexed = index_list midrules in
  List.iter (midrule2rule rules vinfo) midrules_indexed


let add_auxiliary_rules nt_kinds rules =
  let num_of_nts = !ntauxid in
  let nt_kinds' = Array.make num_of_nts ("", O) in
  let rules' = Array.make num_of_nts (0, dummy_term) in
   for i = 0 to Array.length rules - 1 do
      nt_kinds'.(i) <- nt_kinds.(i);
      rules'.(i) <- rules.(i)
   done;
   List.iter (fun (f, arity, body) ->
      rules'.(f) <- (arity, body);
      nt_kinds'.(f) <- ("$NT" ^ string_of_int f, O)
    ) !aux_rules;
   (nt_kinds', rules')

let rec elim_fun_from_midterm vl (term : midterm) newrules : midterm * midrules =
  let MApp (h, pterms) = term in
  let pterms', newrules' = elim_fun_from_midterms vl pterms newrules in
  let MApp (h', pterms''), newrules'' = elim_fun_from_head vl h newrules' in
  (MApp (h', pterms'' @ pterms'), newrules'')
  
and elim_fun_from_midterms vl (terms : midterm list) newrules =
  match terms with
  | [] -> ([], newrules)
  | pterm :: pterms ->
    let pterms',newrules' = elim_fun_from_midterms vl pterms newrules in
    let pterm', newrules'' = elim_fun_from_midterm vl pterm newrules' in
    (pterm' :: pterms', newrules'')
    
and elim_fun_from_head vl (h : midhead) newrules : midterm * midrules =
  match h with
  | MT _ | MNT _ | MVar _ -> (MApp (h, []), newrules)
  | MFun (vl1, pterm) ->
    let vl' = vl @ vl1 in (* what if names in vl and vl1 clashe? *)
    let pterm', newrules' = elim_fun_from_midterm vl' pterm newrules in
    let f = Syntax.new_ntname () in
    let terms1 = List.map (fun v -> MApp (MVar v, [])) vl in
    (MApp (MNT f, terms1), (f, vl', pterm') :: newrules')

let elim_fun_from_midrule (rule : midrule) newrules : midrule * midrules =
  let f, vl, term = rule in
  let term', newrules' = elim_fun_from_midterm vl term newrules in
  ((f, vl, term'), newrules')
  
(** Removes lambdas from bodies of nonterminals. *)
let elim_fun_from_midrules (rules : midrules) : midrules =
  let rules', newrules =
    List.fold_left
      (fun (rules', newrules) rule ->
         let rule', newrules' = elim_fun_from_midrule rule newrules in
         (rule' :: rules', newrules')
      ) ([], []) rules
  in
  List.rev_append rules' newrules

module SS = Set.Make(String)

let b_tree (k : int) (counted : bool) (arg_terms : midterm list) : midterm =
  let rec b_tree_aux from_arg to_arg =
    if from_arg = to_arg then
      MApp (MVar ("_" ^ string_of_int from_arg), [])
    else
      let mid_arg = (from_arg + to_arg) / 2 in
      let args = [b_tree_aux from_arg mid_arg; b_tree_aux (mid_arg + 1) to_arg] in
      MApp (MT B, args)
  in
  let rec vars k acc =
    if k = 0 then
      acc
    else
      vars (k - 1) (("_" ^ string_of_int k) :: acc)
  in
  let (body, wrap_fun) =
    if k = 0 then
      (* converted terminal with no children as _e *)
      (MApp (MT E, []), false)
    else if k = 1 && List.length arg_terms = 1 then
      (* removing identities *)
      (List.hd arg_terms, false)
    else
      (b_tree_aux 1 k, true)
  in
  (* adding _a above counted ones *)
  let body' = if counted then
      MApp (MT A, [body])
    else 
      body
  in
  if wrap_fun then
    MApp (MFun (vars k [], body'), arg_terms)
  else
    body

(** Replaces preterminals with minimal set of standard terminals - _a, _b, _e.
    Checks for name conflicts between variables, terminals, and br. Replacing is done by changing
    terminals of arity k with a lambda-term with _b-tree (with branches) with all k arguments of
    height log2(k)+1. If k=0, the terminal is replaced with _e instead. If the terminal is
    counted, _a is added above that tree. *)
let prerules2midrules (prerules : Syntax.prerules)
    (preterminals : Syntax.preterminals) : midrules =
  (* hashmap for fast access, also checking for conflicts *)
  let preterminals_map = Hashtbl.create 1000 in
  List.iter (fun t ->
      match t with
      | Syntax.Terminal (name, arity, counted) ->
        if Hashtbl.mem preterminals_map name then
          failwith @@ "Terminal " ^ name ^ " defined twice"
        else if name = "br" then
          failwith "Terminal br is reserved for nondeterministic choice"
        else
          Hashtbl.add preterminals_map name (arity, counted)) preterminals;
  let prerule2midrule (nt, args_list, preterm) : midrule =
    let rec preterm2midterm (vars : SS.t) (preterm : Syntax.preterm) : midterm =
      match preterm with
      | Syntax.PApp (head, a) ->
        let arg_preterms = List.map (preterm2midterm vars) a in
        match head with
        | Syntax.Name name ->
          if SS.mem name vars then
            (* converting variables *)
            MApp (MVar name, arg_preterms)
          else if name = "br" then
            (* converting br *)
            MApp(MT B, arg_preterms)
          else
            (* converting terminals *)
            begin
              try
                let arity, counted = Hashtbl.find preterminals_map name in
                if List.length a > arity then
                  failwith @@ "Terminal " ^ name ^ " applied to more arguments than its arity"
                else
                  b_tree arity counted arg_preterms
              with
              | Not_found ->
                failwith @@ "Unbounded name " ^ name ^ " in the body of nonterminal " ^ nt
            end
        (* leaving nonterminals as they were *)
        | Syntax.NT name -> MApp (MNT name, arg_preterms)
        | Syntax.Fun (fvars, preterm) ->
          let fun_args = List.fold_left (fun acc arg ->
              if SS.mem arg acc then
                failwith @@ "Variable " ^ arg ^ " defined twice in function in nonterminal " ^ nt
              else if Hashtbl.mem preterminals_map arg || arg = "br" then
                failwith @@ "Variable " ^ arg ^ " in function in nonterminal " ^ nt ^
                            " conflicts with a terminal with the same name"
              else
                SS.add arg acc
            ) SS.empty fvars
          in
          MApp (MFun (fvars, preterm2midterm (SS.union vars fun_args) preterm),
                      arg_preterms)
    in
    (* set for fast access, also checking for conflicts *)
    let args = List.fold_left (fun acc arg ->
        if SS.mem arg acc then
          failwith @@ "Variable " ^ arg ^ " defined twice in nonterminal " ^ nt
        else if Hashtbl.mem preterminals_map arg || arg = "br" then
          failwith @@ "Variable " ^ arg ^ " in nonterminal " ^ nt ^
                      " conflicts with a terminal with the same name"
        else
          SS.add arg acc
      ) SS.empty args_list
    in
    (nt, args_list, preterm2midterm args preterm)
  in
  List.map prerule2midrule prerules

(** Converts parsed rules into rules with better semantics in the form of a grammar.
    Distinguishes between variables and terminals. Eliminates lambdas from inside of nonterminal
    bodies by replacing them with fresh nonterminals.
    The output grammar has dummy sorts of nonterminals. *)
let prerules2gram
    (prerules, preterminals : Syntax.prerules * Syntax.preterminals) : Grammar.grammar =
  (* terminology:
     * Prerules are rules with terminals as strings.
     * Midrules are rules with terminals converted to a, b, or e.
     * Rules are rules in the format as in the output grammar.
  *)
  let midrules : midrules = prerules2midrules prerules preterminals in
  let midrules = elim_fun_from_midrules midrules in
  let nt_names = List.map (fun (x, _, _) -> x) midrules in
  let num_of_nts = List.length nt_names in
  ntauxid := num_of_nts;
  (* map nt id -> nt name, nt kind *)
  nt_kinds := Array.make num_of_nts (dummy_ntname, O);
  (* assigning a unique number to each nonterminal *)
  List.iter register_nt nt_names;
  (* map nt id -> arity, term *)
  let rules = Array.make num_of_nts (0, dummy_term) in
  let vinfo = Array.make num_of_nts [||] in
  midrules2rules rules vinfo midrules;
  let nt', rules' = 
    if !Flags.normalize then
      add_auxiliary_rules !nt_kinds rules
    else
      (!nt_kinds, rules)
  in
  let g = new Grammar.grammar nt' vinfo rules' in
  (* saving grammar in a global variable *)
  if !Flags.debugging then
    begin
      print_string "Grammar after conversion from prerules:\n";
      g#report_grammar
    end;
  g

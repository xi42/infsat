open Grammar
open Utilities

let nt_kinds = ref (Array.make 0 ("", O))
let ntid = ref 0
let new_nt() =
  let x= !ntid in
   (ntid := x+1; x)

let ntauxid = ref 0
let new_ntaux() =
  let x= !ntauxid in
   (ntauxid := x+1; x)

(** Maps nonterminal names to fresh ids. *)
let tab_ntname2id = Hashtbl.create 1000

let register_nt ntname =
  if Hashtbl.mem tab_ntname2id ntname then raise (DuplicatedNonterminal ntname)
  else 
    let nt = new_nt() in 
     (Hashtbl.add tab_ntname2id ntname nt;
      (!nt_kinds).(nt) <- (ntname,O) (* for the moment, ignore the kind *)
      )
let lookup_ntid ntname =
  try Hashtbl.find tab_ntname2id ntname
  with Not_found -> raise (UndefinedNonterminal ntname)

let aux_rules = ref []
let register_new_rule f arity body =
   aux_rules := (f,arity,body)::!aux_rules

let rec depth_of_term term =
  match term with
    T(_) -> 0
  |NT(_) -> 0
  | Var(_) -> 0
  | App(t1,t2) -> max (depth_of_term t1) (depth_of_term t2+1)



let rec pterm2term vmap pterm =
(** distinguish between variables and terminal symbols **)
  match pterm with
    Syntax.PApp(h, pterms) ->
     let h' = 
       match h with
       | Syntax.Name(s) -> (try Var(List.assoc s vmap) with Not_found -> T(s))
       | Syntax.NT(s) -> NT(lookup_ntid s)
       | Syntax.Fun(_, _) -> assert false
     in
     let terms = List.map (pterm2term vmap) pterms in
     let terms' = if !(Flags.normalize) then
                     List.map normalize_term terms
                  else terms
     in
        mk_app h' terms'

and normalize_term term =
  match term with
    App(_,_) -> (* reduces outer applications *)
        if depth_of_term term > !(Flags.normalization_depth) then
           let vars = vars_in_term term in
           let arity = List.length vars in
           let nt = new_ntaux() in
           let subst = List.combine vars 
                          (List.map (fun i->Var(nt,i)) (fromto 0 arity)) in
           let term' = Grammar.subst_term subst term in
             (register_new_rule nt arity term';
              mk_app (NT(nt)) (List.map (fun i-> Var i) vars))
        else term
  | _ -> term

let dummy_vname = "dummy_var" 

let prerule2rule rules vinfo (f, (_, ss, pterm)) =
  let ss' = indexlist ss in
  let arity = List.length ss in
  let vmap = List.map (fun (i,v) -> (v, (f,i))) ss' in (* [(arg name, (nonterm ix, arg ix)) *)
  let _ = vinfo.(f) <- Array.make arity dummy_vname in
  let _ = List.iter (fun (i,v) -> (vinfo.(f).(i) <- v)) ss' in (* vinfo[nonterm id][arg ix] = arg name *)
  let term = pterm2term vmap pterm in
  rules.(f) <- (arity, term) (* F x_1 .. x_n = t => rules[F] = (n, potentially normalized term with names changed either to var or to terminal) *)

let prerules2rules rules vinfo prerules =
  let prerules_indexed = indexlist prerules in
  List.iter (prerule2rule rules vinfo) prerules_indexed



let dummy_term = NT(0)
let dummy_ntname = "DummyNT"

let add_auxiliary_rules nt_kinds rules =
  let num_of_nts = !ntauxid in
  let nt_kinds' = Array.make num_of_nts ("",O) in
  let rules' = Array.make num_of_nts (0,dummy_term) in
   for i=0 to Array.length rules -1 do
      nt_kinds'.(i) <- nt_kinds.(i);
      rules'.(i) <- rules.(i)
   done;
   List.iter (fun (f,arity,body) ->
      rules'.(f) <- (arity, body);
      nt_kinds'.(f) <- ("$NT"^(string_of_int f), O)
      ) 
      !aux_rules;
   (nt_kinds', rules')

let rec elim_fun_from_preterm vl preterm newrules =
  let Syntax.PApp(h, pterms) = preterm in
  let (pterms',newrules') = elim_fun_from_preterms vl pterms newrules in
  let (Syntax.PApp(h',pterms''), newrules'') =
         elim_fun_from_head vl h newrules' in
     (Syntax.PApp(h', pterms''@pterms'), newrules'')
and elim_fun_from_preterms vl preterms newrules =
  match preterms with
    [] -> ([], newrules)
  | pterm::pterms ->
      let (pterms',newrules') = elim_fun_from_preterms vl pterms newrules in
      let (pterm', newrules'') = elim_fun_from_preterm vl pterm newrules' in
         (pterm'::pterms', newrules'')
and elim_fun_from_head vl h newrules =
  match h with
    Syntax.Name(s) -> (Syntax.PApp(Syntax.Name(s),[]), newrules)
  | Syntax.NT(s) -> (Syntax.PApp(Syntax.NT(s),[]), newrules)
  | Syntax.Fun(vl1,pterm) ->
       let vl' = vl@vl1 in (* what if names in vl and vl1 clashe? *)
       let (pterm',newrules') = elim_fun_from_preterm vl' pterm newrules in
       let f = Syntax.new_ntname() in
       let pterms1 = List.map (fun v -> Syntax.PApp(Syntax.Name(v), [])) vl in
         (Syntax.PApp(Syntax.NT(f), pterms1), (f, vl', pterm')::newrules')

let elim_fun_from_prerule prerule newrules =
  let (f, vl, preterm) = prerule in
  let (preterm', newrules')= elim_fun_from_preterm vl preterm newrules in
    ((f,vl,preterm'), newrules')

(** Removes lambdas from bodies of nonterminals. *)
let elim_fun_from_prerules prerules =
 let (prerules', newrules) =
  ( List.fold_left
   (fun (prerules',newrules) prerule ->
      let (prerule',newrules')=
          elim_fun_from_prerule prerule newrules
      in (prerule'::prerules', newrules'))
   ([], [])
   prerules)
 in List.rev_append prerules' newrules

module SS = Set.Make(String)

type abc_atom = AVar of string | ANT of string | A | B | C
type abc_prerule = AApp of abc_atom * abc_prerule list

let b_tree k =
  assert (k >= 1);
  let rec b_tree_aux from_arg to_arg =
    if from_arg = to_arg then
      Syntax.PApp(Syntax.Name("_"^(string_of_int from_arg)), [])
    else
      let mid_arg = (from_arg + to_arg) / 2 in
      let args = [b_tree_aux from_arg mid_arg; b_tree_aux (mid_arg + 1) to_arg] in
      Syntax.PApp(Syntax.Name("_b"), args)
  in
  let rec vars k acc =
    if k = 0 then
      acc
    else
      vars (k-1) (("_"^(string_of_int k))::acc)
  in
  Syntax.Fun(vars k [], b_tree_aux 1 k)

(** Replaces preterminals with minimal set of standard terminals - _a, _b, _c.
    Checks for name conflicts between variables, terminals, and br. Replacing is done by changing
    terminals of arity k with a lambda-term with _b-tree (with branches) with all k arguments of
    height log2(k)+1. If k=0, the terminal is replaced with _c instead. If the terminal is
    counted, _a is added above that tree. *)
let terminals2abc prerules preterminals =
  (* hashmap for fast access, also checking for conflicts *)
  let preterminals_map = Hashtbl.create 1000 in
  List.iter (fun t -> match t with
      | Syntax.Terminal(name, arity, counted) ->
        if Hashtbl.mem preterminals_map name then
          failwith ("Terminal "^name^" defined twice")
        else if name = "br" then
          failwith ("Terminal br is reserved for nondeterministic choice")
        else
          Hashtbl.add preterminals_map name (arity, counted)) preterminals;
  let terminals2abc_prerule (nt, args_list, preterm) =
    (* set for fast access, also checking for conflicts *)
    let args = List.fold_left (fun acc arg ->
        if SS.mem arg acc then
          failwith ("Variable "^arg^" defined twice in nonterminal "^nt)
        else if Hashtbl.mem preterminals_map arg || arg = "br" then
          failwith ("Variable "^arg^" in nonterminal "^nt^" conflicts with a terminal with "^
                    "the same name")
        else
          SS.add arg acc) SS.empty args_list
    in
    let rec terminals2abc_preterm args preterm =
      match preterm with
      | Syntax.PApp(head, a) ->
        let arg_preterms = List.map (terminals2abc_preterm args) a in
        match head with
        | Syntax.Name(name) ->
          if SS.mem name args then
            (* leaving variables and br as they were *)
            Syntax.PApp(head, arg_preterms)
          else if name = "br" then
            (* converting br *)
            Syntax.PApp(Syntax.Name("_b"), arg_preterms)
          else
            (* converting terminals *)
            (try
               let (arity, counted) = Hashtbl.find preterminals_map name in
               if List.length a > arity then
                 failwith ("Terminal "^name^" applied to more arguments than its arity")
               else
                 (* converted terminal as _c or as a function *)
                 let terminal_app =
                   if List.length a = 1 && arity = 1 then
                     (* removing identities *)
                     List.hd arg_preterms
                   else
                     let terminal_fun =
                       if arity = 0 then
                         Syntax.Name("_c")
                       else
                         b_tree arity
                     in
                     Syntax.PApp(terminal_fun, arg_preterms)
                 in
                 (* adding _a above counted ones *)
                 if counted then
                   Syntax.PApp(Syntax.Name("_a"), [terminal_app])
                 else
                   terminal_app
             with Not_found ->
               failwith ("Unbounded name "^name^" in the body of nonterminal "^nt)
            )
        (* leaving nonterminals as they were *)
        | Syntax.NT(_) -> Syntax.PApp(head, arg_preterms)
        | Syntax.Fun(vars, preterm) ->
          let fun_args = List.fold_left (fun acc arg ->
              if SS.mem arg acc then
                failwith ("Variable "^arg^" defined twice in function in nonterminal "^nt)
              else if Hashtbl.mem preterminals_map arg || arg = "br" then
                failwith ("Variable "^arg^" in function in nonterminal "^nt^" conflicts with a "^
                          "terminal with the same name")
              else
                SS.add arg acc) SS.empty vars
          in
          Syntax.PApp(Syntax.Fun(vars, terminals2abc_preterm (SS.union args fun_args) preterm),
                      arg_preterms)
    in
    (nt, args_list, terminals2abc_preterm args preterm)
  in
  List.map terminals2abc_prerule prerules

(** Converts parsed rules into rules with better semantics.
    Distinguishes between variables and terminals. Adds additional arguments so that body of a
    rule has kind O. TODO complete docs. *)
let prerules2gram (prerules, preterminals) =
  let prerules = terminals2abc prerules preterminals in
  if !Flags.debugging then
    print_string ("Input after converting terminals:\n"^(Syntax.string_of_prerules prerules)^"\n");
  let prerules = elim_fun_from_prerules prerules in
  let nt_names = List.map (fun (x,_,_) -> x) prerules in
  let num_of_nts = List.length nt_names in
  let _ = (ntauxid := num_of_nts) in
  (* map nt id -> nt name, nt kind *)
  let _ = nt_kinds := Array.make num_of_nts (dummy_ntname, O) in
  (* assigning a unique number to each nonterminal *)
  let _ = List.iter register_nt nt_names in
  (* map nt id -> arity, term *)
  let rules = Array.make num_of_nts (0,dummy_term) in
  let vinfo = Array.make num_of_nts [| |] in
  let _ = prerules2rules rules vinfo prerules in
  let (nt', rules') = 
    if !(Flags.normalize) then
      add_auxiliary_rules !nt_kinds rules
    else (!nt_kinds, rules)
  in
  let s = 0 in
  let terminals = List.map (fun a -> (a, -1)) (terminals_in_rules rules) in
  let g = {nt= nt'; t=terminals; vinfo = vinfo; r=rules'; s=s} in
  Grammar.gram := g; (* here the grammar is put into a global variable - TODO remove that *)
  if !Flags.debugging then
    begin
      print_string "Grammar after conversion from prerules:\n";
      Grammar.report_grammar g
    end;
  g

(*
let states_in_tr ((q, a), qs) =
  let qs' = delete_duplication (List.sort compare qs) in
    merge_and_unify compare [q] qs'
let rec states_in_transitions transitions =
 match transitions with
   [] -> []
 | tr::transitions' ->
     merge_and_unify compare (states_in_tr tr) (states_in_transitions transitions')

let get_rank_from_tr ((q,a),qs) =
  (a, List.length qs)
let rec insert_rank (a,k) alpha =
  match alpha with
    [] -> [(a,k)]
  | (a',k')::alpha' ->
       let x = compare a a' in
         if x<0 then (a,k)::alpha
         else if x=0 then if k=k' then alpha else raise (InconsistentArity a)
         else (a',k')::(insert_rank (a,k) alpha')

(** List of arities and letters, descending. Check if arities consistent for letters. *)
let rec get_rank_from_transitions trs =
  match trs with
   [] -> []
  | tr::trs' ->
     insert_rank (get_rank_from_tr tr) (get_rank_from_transitions trs')

let rec merge_rank alpha1 alpha2 =
  match (alpha1,alpha2) with
   ([], _) -> alpha2
 | (_, []) -> alpha1
 | ((a1,k1)::alpha1', (a2,k2)::alpha2') ->
    let x = compare a1 a2 in
     if x<0 then (a1,k1)::(merge_rank alpha1' alpha2)
     else if x>0 then (a2,k2)::(merge_rank alpha1 alpha2')
     else (a1, max k1 k2)::(merge_rank alpha1' alpha2')

let convert (prerules, transitions) =
  let g = prerules2gram prerules in
  let q0 = fst (fst (List.hd transitions)) in
  let states = states_in_transitions transitions in
  let alpha1 = get_rank_from_transitions transitions in (* compute letter arities *)
  let alpha1' = merge_rank alpha1 g.t in (* merge letter arities with info from grammar *)
  let m = {alpha=alpha1'; st=states; delta=transitions; init=q0} in (* create automaton *)
     (g, m)

open AlternatingAutomaton;;
let convert_ata (prerules, ranks, transitions ) =
(*  let open AlternatingAutomaton in *)
  let g = prerules2gram prerules in
  let m = from_transitions (ranks,transitions) in
  (g, m);;
(** END: conversion from parsing results **)
*)

open GrammarCommon
open HGrammar
open Utilities

type order = int

let rec order : sort -> int = function
  | SAtom -> 0
  | SFun (s1, s2) -> max (1 + order s1) (order s2)

(** Returns either description of why term safety is violated or minimum order of a variable. *)
let rec check_hterm_safety (hg : hgrammar) (h, ids : hterm) : (string, order) either =
  let head_var_order : order = match h with
    | HT _ -> max_int
    | HNT nt -> max_int
    | HVar v -> order @@ hg#var_sort v
  in
  let min_var_order : (string, order) either =
    List.fold_left (fun min_var_order id ->
        List.fold_left (fun min_var_order hterm ->
            match min_var_order with
            | Right min_var_order ->
              begin
                match check_hterm_safety hg hterm with
                | Right hterm_max_var_order ->
                  Right (min min_var_order hterm_max_var_order)
                | Left message as msg -> msg
              end
            | Left _ -> min_var_order
          ) min_var_order @@ hg#id2hterms id
      ) (Right head_var_order) ids
  in
  match min_var_order with
  | Right min_var_order ->
    let head_sort = match h with
      | HT a -> sort_of_terminal a
      | HNT nt -> hg#nt_sort nt
      | HVar v -> hg#var_sort v
    in
    let arg_count =
      List.fold_left (fun acc id ->
          acc + List.length (hg#id2hterms id)
        ) 0 ids
    in
    (* sort of application after removing sorts of arg_count arguments *)
    let term_sort : sort ref = ref head_sort in
    for i = 0 to arg_count - 1 do
      match !term_sort with
      | SFun (_, codomain) ->
        term_sort := codomain
      | SAtom ->
        failwith "Expected a function sort"
    done;
    let term_order : order = order !term_sort in
    if min_var_order < term_order then
      Left ("Encountered term " ^ hg#string_of_hterm false HlocMap.empty 0 (h, ids) ^
            " with sort " ^ string_of_sort !term_sort ^ " of order " ^ string_of_int term_order ^
            ", while minimum order of sort " ^
            "of a variable in this term was " ^ string_of_int min_var_order ^ ".")
    else
      Right min_var_order
  | Left _ -> min_var_order

(** Returns string with location description if one of terms in the grammar is not safe,
    otherwise returns None. *)
let check_safety (hg : hgrammar) : string option =
  List.fold_left (fun safe nt ->
      match safe with
      | Some _ -> safe
      | None ->
        let hterm = hg#nt_body nt in
        match check_hterm_safety hg hterm with
        | Left message -> Some message
        | Right _ -> None
    ) None @@ range 0 hg#nt_count
    

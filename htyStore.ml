open GrammarCommon
open HGrammar
open Type
open TypingCommon
open Utilities

(* TODO this should be a data structure with fast merge of 1 element and iteration, not
   necessarity ordered - maybe ity list hashset array or radix tree like in horsat, maybe some
   custom optimization for adding products would be useful *)
(** Mapping from hterms ids to possible typings of these hterms. *)
class hty_store (hgrammar : hgrammar) = object(self)
  (* --- data --- *)

  (** hterms_itys[id][i][j] is intersection types that hterms with identifier id have in i-th known
      typing in position j. *)
  val htys : HtySet.t array = Array.make hgrammar#hterms_count HtySet.empty

  (* --- access --- *)

  method get_htys (id : hterms_id) : HtySet.t = htys.(id)

  (* --- modification --- *)

  (* TODO this should be array hterms_id -> set of hty, also ty funs should change to arg list -> res *)

  (** Idempodently adds mapping from id to hty to the storage. Returns whether it was new (did not
      already exist). *)
  method add_hty (id : hterms_id) (hty : hty) : bool =
    let hterms_htys = htys.(id) in
    if HtySet.mem hty hterms_htys then
      false
    else
      begin
        htys.(id) <- HtySet.add hty hterms_htys;
        true
      end
end

let remove_hty_duplicates (htys : hty list) : hty list =
  Utilities.delete_consecutive_duplicates compare @@ List.sort hty_compare htys

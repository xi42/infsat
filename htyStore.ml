open GrammarCommon
open HGrammar
open Type
open Utilities

(* TODO this should be a data structure with fast merge of 1 element and iteration, not
   necessarity ordered - maybe ity list hashset array or radix tree like in horsat, maybe some
   custom optimization for adding products would be useful *)
(** Mapping from hterms ids to possible typings of these hterms. *)
class hty_store (hgrammar : hgrammar) = object(self)
  (* --- data --- *)

  (** hterms_itys[id][i][j] is intersection types that hterms with identifier id have in i-th known
      typing in position j. *)
  val htys : hty list array = Array.make hgrammar#hterms_count []

  (* --- access --- *)

  method get_htys (id : hterms_id) : hty list = htys.(id)

  (* --- modification --- *)

  method add_hty (id : hterms_id) (hty : hty) =
    let htys' = htys.(id) in
    if not @@ List.exists (hty_eq hty) htys' then
      htys.(id) <- hty :: htys'
end

let remove_hty_duplicates (htys : hty list) : hty list =
  Utilities.delete_consecutive_duplicates Pervasives.compare @@ List.sort hty_compare htys

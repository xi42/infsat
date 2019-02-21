open GrammarCommon
open HGrammar
open Type
open Utilities

(** Typing of each of hterm's arguments. *)
type hty = ity list

(** Lexicographical order on hty. *)
let rec hty_compare hty1 hty2 =
  match hty1, hty2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | ity1 :: hty1', ity2 :: hty2' ->
    let ci = TyList.compare ity1 ity2 in
    if ci <> 0 then
      ci
    else
      hty_compare hty1' hty2'

let rec hty_eq hty1 hty2 = hty_compare hty1 hty2 = 0

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

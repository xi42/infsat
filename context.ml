open GrammarCommon
open HGrammar
open Type
open TypingCommon
open Utilities

type bix = int
module BixMap = IntMap
module BixSet = IntSet
module HtermsMap = IntMap

(** Compressed collection of possible types of variables and nonterminals. Its two main features
    are keeping possible typings of hterms in the form of a product instead of product's elements
    as long as possible and imposing a restriction that given typing of a nonterminal or hterms
    has to be used at least once in a short-circuit-friendly way. *)
type ctx = {
  (** Mapping from variable positions (i.e., without nonterminal) to position of hterms they're in
      in the processed binding (binding index) and position of variable in these hterms. *)
  var_bix : (bix * int) IntMap.t;
  (** Mapping from binding index to possible htys for the hterms represented by it. *)
  bix_htys : HtySet.t BixMap.t;
  (** Optional restriction that one of hterms with bix from given set must have types hty.
      It is assumed (and not checked) that hterms with bix from that set have possible types hty
      in bix_htys. If this set is empty then it means that the restriction can't be satisfied
      and this context is empty. *)
  forced_hterms_hty : (BixSet.t * hty) option;
  (** Possible types for nonterminals. *)
  nt_ity : ity array;
  (** Optional restriction that one of nonterminals in given locations needs to have type ty.
      It is assumed (and not checked) that nonterminals in these locations have possible type
      ty in nt_ity. If this set is empty then it means that the restriction can't be satisfied
      and this context is empty. *)
  forced_nt_ty : (HlocSet.t * ty) option
}

(** Normalize the context, i.e., remove non-forced typings for given binding index (bix) if it
    is the last one with possible forced typing. There is no need for such cleanup in the case of
    nonterminals, since these are processed by location and each location is processed at most
    once. *)
let ctx_normalize (ctx : ctx) : ctx =
  let bix_htys =
    match ctx.forced_hterms_hty with
    | Some (bixs, hty) ->
      if BixSet.cardinal bixs = 1 then
        let bix = BixSet.choose bixs in
        BixMap.add bix (HtySet.singleton hty) ctx.bix_htys
      else
        ctx.bix_htys
    | None -> ctx.bix_htys
  in
  { ctx with bix_htys = bix_htys }

let mk_ctx (var_bix : (bix * int) IntMap.t) (bix_htys : hty list BixMap.t)
    (forced_hterms_hty : (bix list * hty) option)
    (nt_ity : ity array) (forced_nt_ty : (hloc list * ty) option) : ctx =
  let ctx = {
    var_bix = var_bix;
    bix_htys = BixMap.map HtySet.of_list bix_htys;
    forced_hterms_hty = option_map (fun (bixs, hty) ->
        (BixSet.of_list bixs, hty)
      ) forced_hterms_hty;
    nt_ity = nt_ity;
    forced_nt_ty = option_map (fun (hlocs, ty) ->
        (HlocSet.of_list hlocs, ty)
      ) forced_nt_ty
  } in
  ctx_normalize ctx

(** The number of different var typings possible to generate in the current environment. *)
let ctx_var_combinations (ctx : ctx) : int =
  match ctx.forced_hterms_hty with
  | None ->
    IntMap.fold (fun _ htys acc -> acc * (HtySet.cardinal htys)) ctx.bix_htys 1
  | Some (fbixs, fhty) ->
    let non_forced_cat_comb, forced_mul, forced_wrong_mul =
      IntMap.fold (fun bix htys (nfc, fc, fcw) ->
          let s = HtySet.cardinal htys in
          if BixSet.mem bix fbixs then
            begin
              assert (HtySet.mem fhty htys);
              (nfc, fc * s, fcw * (s - 1))
            end
          else
            (nfc * s, fc, fcw)
        ) ctx.bix_htys (1, 1, 1)
    in
    non_forced_cat_comb * (forced_mul - forced_wrong_mul)

(** Decreases ctx.bix_htys to its subset htys. *)
let ctx_shrink_htys (ctx : ctx) (bix : bix) (htys : HtySet.t) : ctx list =
  if HtySet.is_empty htys then
    []
  else
    let bix_htys = IntMap.add bix htys ctx.bix_htys in
    match ctx.forced_hterms_hty with
    | None ->
      [{ ctx with bix_htys = bix_htys }]
    | Some (fbixs, fhty) ->
      if BixSet.mem bix fbixs then
        if not @@ HtySet.mem fhty htys then
          let fbixs = BixSet.remove bix fbixs in
          if BixSet.is_empty fbixs then
            (* requirement can't be satisfied for this bix anymore and it was the last bix *)
            []
          else
            (* requirement can't be satisfied, but there are more bixs *)
            let ctx = { ctx with bix_htys = bix_htys; forced_hterms_hty = Some (fbixs, fhty) } in
            [ctx_normalize ctx]
        else if HtySet.cardinal htys = 1 then
          (* requirement was satisfied *)
          [{ ctx with bix_htys = bix_htys; forced_hterms_hty = None }]
        else
          (* requirement can still be satisfied, but there are less hty options now *)
          [{ ctx with bix_htys = bix_htys }]
      else
        [{ ctx with bix_htys = bix_htys }]

let ctx_split_var (ctx : ctx) (_, v : var_id) : (ty * ctx) list =
  let bix, i = IntMap.find v ctx.var_bix in
  let htys = IntMap.find bix ctx.bix_htys in
  (* splitting htys by type of i-th variable in them *)
  let ty_htys : HtySet.t TyMap.t =
    HtySet.fold (fun hty acc ->
        let ity = List.nth hty i in
        TyList.fold_left (fun acc ty ->
            let htys =
              match TyMap.find_opt ty acc with
              | Some htys -> HtySet.add hty htys
              | None -> HtySet.singleton hty
            in
            TyMap.add ty htys acc
          ) acc ity
      ) htys TyMap.empty
  in
  TyMap.fold (fun ty htys acc ->
      let ty_ctx = List.map (fun ctx -> (ty, ctx)) @@ ctx_shrink_htys ctx bix htys in
      ty_ctx @ acc
    ) ty_htys []

(** Create a new compressed product like this, but where variable v satisfies f. *)
let ctx_enforce_var (ctx : ctx) (_, v : var_id) (ty : ty) : (ty * ctx) list =
  let bix, i = IntMap.find v ctx.var_bix in
  let htys = IntMap.find bix ctx.bix_htys in
  let htys =
    HtySet.filter (fun hty ->
        TyList.exists (Ty.equal ty) (List.nth hty i)
      ) htys
  in
  List.map (fun ctx -> (ty, ctx)) @@ ctx_shrink_htys ctx bix htys

let ctx_split_nt (ctx : ctx) (nt : nt_id) (loc : hloc) : (ty * ctx) list =
  match ctx.forced_nt_ty with
  | Some (flocs, fty) ->
    if HlocSet.mem loc flocs then
      TyList.filter_map (fun ty ->
          if Ty.equal ty fty then
            (* requirement was satisfied *)
            Some (ty, { ctx with forced_nt_ty = None })
          else
            let flocs = HlocSet.remove loc flocs in
            if HlocSet.is_empty flocs then
              (* requirement was not satisfied and it was the last chance *)
              None
            else
              (* requirement was not satisfied, but there are more options *)
              Some (ty, { ctx with forced_nt_ty = Some (flocs, fty) })
        ) ctx.nt_ity.(nt)
    else
      TyList.map (fun ty -> (ty, ctx)) ctx.nt_ity.(nt)
  | None ->
    TyList.map (fun ty -> (ty, ctx)) ctx.nt_ity.(nt)

let ctx_enforce_nt (ctx : ctx) (loc : hloc) (ty : ty) : (ty * ctx) list =
  match ctx.forced_nt_ty with
  | Some (flocs, fty) ->
    if HlocSet.mem loc flocs then
      if Ty.equal ty fty then
        (* requirement was satisfied *)
        [(ty, { ctx with forced_nt_ty = None })]
      else
        let flocs = HlocSet.remove loc flocs in
        if HlocSet.is_empty flocs then
          (* requirement was not satisfied and it was the last position *)
          []
        else
          (* requirement was not satisfied, but there are more positions *)          
          [(ty, { ctx with forced_nt_ty = Some (flocs, fty) })]
    else
      [(ty, ctx)]
  | None ->
    [(ty, ctx)]

exception EmptyIntersection

let intersect_ctxs (ctx1 : ctx) (ctx2 : ctx) : ctx option =
  try
    let bix_htys =
      BixMap.merge (fun _ htys1 htys2 ->
          match htys1, htys2 with
          | None, _ | _, None -> failwith "Context keys differ."
          | Some htys1, Some htys2 ->
            let htys = HtySet.inter htys1 htys2 in
            (* If it becomes empty due to intersection but wasn't empty before,
               there are conflicting assumptions. *)
            if HtySet.is_empty htys && not (HtySet.is_empty htys1 && HtySet.is_empty htys2) then
              raise EmptyIntersection
            else
              Some htys
        ) ctx1.bix_htys ctx2.bix_htys
    in
    let forced_hterms_hty =
      match ctx1.forced_hterms_hty, ctx2.forced_hterms_hty with
      | None, _ | _, None -> None
      | Some (bixs1, hty), Some (bixs2, _) ->
        let bixs = BixSet.inter bixs1 bixs2 in
        if BixSet.is_empty bixs then
          raise_notrace EmptyIntersection
        else if bixs |> BixSet.exists (fun bix ->
            1 = HtySet.cardinal @@ BixMap.find bix bix_htys) then
          (* Due to intersection, the requirement was satisfied. *)
          None
        else
          Some (bixs, hty)
    in
    let forced_nt_ty =
      match ctx1.forced_nt_ty, ctx2.forced_nt_ty with
      | None, _ | _, None -> None
      | Some (flocs1, fty), Some (flocs2, _) ->
        let flocs = HlocSet.inter flocs1 flocs2 in
        if HlocSet.is_empty flocs then
          raise_notrace EmptyIntersection
        else
          Some (flocs, fty)
    in
    let ctx = {
      var_bix = ctx1.var_bix;
      bix_htys = bix_htys;
      forced_hterms_hty = forced_hterms_hty;
      nt_ity = ctx1.nt_ity;
      forced_nt_ty = forced_nt_ty
    } in
    Some (ctx_normalize ctx)
  with
  | EmptyIntersection -> None

let ctx_requirements_satisfied ctx : bool =
  ctx.forced_hterms_hty = None && ctx.forced_nt_ty = None

(** Compares two product environments. Only takes the mutable bix_hty and set in
    forced_nt_ty into account. forced_hterms_hty could be computed from common ancestor
    one and bix_htys. *)
let ctx_compare (ctx1 : ctx) (ctx2 : ctx) : int =
  compare_pair
    (BixMap.compare HtySet.compare)
    (option_compare HlocSet.compare)
    (ctx1.bix_htys, option_map fst ctx1.forced_nt_ty)
    (ctx2.bix_htys, option_map fst ctx2.forced_nt_ty)

let ctx_equal (ctx1 : ctx) (ctx2 : ctx) : bool =
  ctx_compare ctx1 ctx2 = 0

(** Empty context for testing purposes. *)
let empty_ctx : ctx = mk_ctx IntMap.empty BixMap.empty None [||] None

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_FseDecomp HufPure_HufStats HufPure_HufX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition X2_WKSP_SIZE : Z := 12 * 13 * 4 + 13 * 4 + 15 * 4 + 256 + 256 + 219 * 4.

(* [comment removed for export] *)
Definition build_x2 (symbol nbBits baseSeq level : Z) : deltX2 :=
  let seq := (if level =? 1 then symbol else baseSeq + symbol * 256) in
  let v := u32 (seq + nbBits * 2^16 + level * 2^24) in
  mkX2 (v mod 2^16) ((v / 2^16) mod 256) ((v / 2^24) mod 256).

Definition ostore2 (l : list (option deltX2)) (i : Z) (v : deltX2) : res (list (option deltX2)) :=
  if (0 <=? i) && (i <? Zlength l) then
    Ok (firstn (Z.to_nat i) l ++ Some v :: skipn (S (Z.to_nat i)) l)
  else Ub.

(* [comment removed for export] *)
Fixpoint store_run (k : nat) (dt : list (option deltX2)) (p : Z) (c : deltX2) : res (list (option deltX2)) :=
  match k with
  | O => Ok dt
  | S k' => let! dt' := ostore2 dt p c in store_run k' dt' (p + 1) c
  end.

(* [comment removed for export] *)
Definition rv_idx (consumed w : Z) : Z := consumed * 13 + w.

Section TableX2.
  Variable L : Z.
  Variable src : list Z.
  Variable wkspSize : Z.
  Let ncells : Z := 2^L.

  (* [comment removed for export] *)
  Fixpoint find_maxW (fuel : nat) (w : Z) (rank : list Z) : res Z :=
    match fuel with
    | O => NoFuel
    | S f => let! c := load rank w in if c =? 0 then find_maxW f (w - 1) rank else Ok w
    end.

  (* [comment removed for export] *)
  Fixpoint rank_start2 (fuel : nat) (w next : Z) (rank : list Z) (rs0 : list Z) : res (list Z * Z) :=
    match fuel with
    | O => Ok (rs0, next)
    | S f =>
      let! c := load rank w in
      let! rs0' := store rs0 (w + 1) next in
      rank_start2 f (w + 1) (u32 (next + c)) rank rs0'
    end.

  (* [comment removed for export] *)
  Fixpoint sort2 (fuel : nat) (s : Z) (ws : list Z) (rs0 : list Z) (sorted : list (option Z)) : res (list Z * list (option Z)) :=
    match fuel with
    | O => Ok (rs0, sorted)
    | S f =>
      let! w := load ws s in
      let! r := load rs0 (w + 1) in
      let! rs0' := store rs0 (w + 1) (u32 (r + 1)) in
      let! sorted' := ostore sorted r s in
      sort2 f (s + 1) ws rs0' sorted'
    end.

  (* [comment removed for export] *)
  Fixpoint rank_val0 (fuel : nat) (w next rescale : Z) (rank : list Z) (rv : list Z) : res (list Z) :=
    match fuel with
    | O => Ok rv
    | S f =>
      let! c := load rank w in
      let! t := shl32 c (u32 (w + rescale)) in
      let! rv' := store rv (rv_idx 0 w) next in
      rank_val0 f (w + 1) (u32 (next + t)) rescale rank rv'
    end.

  (* [comment removed for export] *)
  Fixpoint rank_val_row (fuel : nat) (consumed w : Z) (rv : list Z) : res (list Z) :=
    match fuel with
    | O => Ok rv
    | S f =>
      let! v := load rv (rv_idx 0 w) in
      let! _ := assert (consumed <? 12) in
      let! t := shr32 v consumed in
      let! rv' := store rv (rv_idx consumed w) t in
      rank_val_row f consumed (w + 1) rv'
    end.
  Fixpoint rank_val_rows (fuel : nat) (consumed maxW : Z) (rv : list Z) : res (list Z) :=
    match fuel with
    | O => Ok rv
    | S f =>
      let! rv' := rank_val_row (Z.to_nat maxW) consumed 1 rv in
      rank_val_rows f (consumed + 1) maxW rv'
    end.

  (* [comment removed for export] *)
  Fixpoint fill_for_weight (fuel : nat) (dt : list (option deltX2)) (base : Z) (b e : Z)
           (nbBits targetLog baseSeq level : Z) (sorted : list (option Z)) : res (list (option deltX2) * Z) :=
    match fuel with
    | O => Ok (dt, base)
    | S f =>
      if b =? e then Ok (dt, base)
      else
        let! lsh := Ok (Z.land (targetLog - nbBits) 31) in
        let! length := shl32 1 lsh in
        let! sym := oload sorted b in
        let c := build_x2 sym nbBits baseSeq level in
        let! dt' := store_run (Z.to_nat length) dt base c in
        fill_for_weight f dt' (base + length) (b + 1) e nbBits targetLog baseSeq level sorted
    end.

  (* [comment removed for export] *)
  Fixpoint level2_weights (fuel : nat) (dt : list (option deltX2)) (base : Z) (w maxWeight1 : Z)
           (targetLog consumed : Z) (rv : list Z) (sorted : list (option Z)) (rs0 : list Z)
           (nbBitsBaseline baseSeq : Z) : res (list (option deltX2)) :=
    match fuel with
    | O => Ok dt
    | S f =>
      if w <? maxWeight1 then
        let! b := load rs0 w in
        let! e := load rs0 (w + 1) in
        let nbBits := nbBitsBaseline - w in
        let totalBits := nbBits + consumed in
        let! off := load rv (rv_idx consumed w) in
        let! r := fill_for_weight (S (Z.to_nat (e - b))) dt (base + off) b e totalBits targetLog baseSeq 2 sorted in
        let '(dt', _) := r in
        level2_weights f dt' base (w + 1) maxWeight1 targetLog consumed rv sorted rs0 nbBitsBaseline baseSeq
      else Ok dt
    end.

  Definition level2 (dt : list (option deltX2)) (base : Z) (targetLog consumed : Z) (rv : list Z)
             (minWeight maxWeight1 : Z) (sorted : list (option Z)) (rs0 : list Z) (nbBitsBaseline baseSeq : Z)
    : res (list (option deltX2)) :=
    let! dt1 :=
      (if 1 <? minWeight then
         let! length := shl32 1 (Z.land (targetLog - consumed) 31) in
         let c := build_x2 baseSeq consumed 0 1 in
         let! skipSize := load rv (rv_idx consumed minWeight) in
         if length =? 2 then store_run 2 dt base c
         else if length =? 4 then store_run 4 dt base c
         else (* [comment removed for export] *)
           store_run (Z.to_nat (8 * ((skipSize + 7) / 8))) dt base c
       else Ok dt) in
    level2_weights (Z.to_nat maxWeight1) dt1 base minWeight maxWeight1 targetLog consumed rv sorted rs0 nbBitsBaseline baseSeq.

  (* [comment removed for export] *)
  Fixpoint fill_two_level (fuel : nat) (dt : list (option deltX2)) (s e start length : Z)
           (targetLog nbBits minWeight wEnd : Z) (rv : list Z) (sorted : list (option Z)) (rs0 : list Z) (nbBitsBaseline : Z)
    : res (list (option deltX2)) :=
    match fuel with
    | O => Ok dt
    | S f =>
      if s =? e then Ok dt
      else
        let! sym := oload sorted s in
        let! dt' := level2 dt start targetLog nbBits rv minWeight wEnd sorted rs0 nbBitsBaseline sym in
        fill_two_level f dt' (s + 1) e (start + length) length targetLog nbBits minWeight wEnd rv sorted rs0 nbBitsBaseline
    end.

  (* [comment removed for export] *)
  Fixpoint fill_x2 (fuel : nat) (dt : list (option deltX2)) (w wEnd targetLog : Z) (rv : list Z)
           (sorted : list (option Z)) (rs0 : list Z) (nbBitsBaseline : Z) : res (list (option deltX2)) :=
    match fuel with
    | O => Ok dt
    | S f =>
      if w <? wEnd then
        let maxWeight := wEnd - 1 in
        let scaleLog := nbBitsBaseline - targetLog in
        let minBits := nbBitsBaseline - maxWeight in
        let! b := load rs0 w in
        let! e := load rs0 (w + 1) in
        let nbBits := nbBitsBaseline - w in
        let! dt' :=
          (if minBits <=? targetLog - nbBits then
             let! start := load rv (rv_idx 0 w) in
             let! length := shl32 1 (Z.land (targetLog - nbBits) 31) in
             let minWeight := Z.max 1 (nbBits + scaleLog) in
             fill_two_level (S (Z.to_nat (e - b))) dt b e start length targetLog nbBits minWeight wEnd rv sorted rs0 nbBitsBaseline
           else
             let! start := load rv (rv_idx 0 w) in
             let! r := fill_for_weight (S (Z.to_nat (e - b))) dt start b e nbBits targetLog 0 1 sorted in
             let '(dt1, _) := r in Ok dt1) in
        fill_x2 f dt' (w + 1) wEnd targetLog rv sorted rs0 nbBitsBaseline
      else Ok dt
    end.

  (* [comment removed for export] *)
  Definition read_dtable_x2 : res (Z * list (option deltX2) * Z) :=
    if wkspSize <? X2_WKSP_SIZE then Err ZSTD_error_GENERIC
    else if 12 <? L then Err ZSTD_error_tableLog_tooLarge
    else
      let! h := read_stats src in
      let tableLog := hs_tableLog h in
      if L <? tableLog then Err ZSTD_error_tableLog_tooLarge
      else
        let maxTableLog := (if (tableLog <=? 11) && (11 <? L) then 11 else L) in
        let rank := hs_rank h in
        let! maxW := find_maxW (S (Z.to_nat tableLog)) tableLog rank in
        let! rsn := rank_start2 (Z.to_nat maxW) 1 0 rank (repeat 0 15) in
        let '(rs0a, next) := rsn in
        let! rs0b := store rs0a (0 + 1) next in          (* [comment removed for export] *)
        let! rs0c := store rs0b (maxW + 1 + 1) next in   (* [comment removed for export] *)
        let! sr := sort2 (Z.to_nat (hs_nbSymbols h)) 0 (hs_weights h) rs0c (repeat None 256) in
        let '(rs0d, sorted) := sr in
        let! rs0 := store rs0d (0 + 1) 0 in               (* [comment removed for export] *)
        let rescale := maxTableLog - tableLog - 1 in
        let! rv0 := rank_val0 (Z.to_nat maxW) 1 0 rescale rank (repeat 0 (12 * 13)) in
        let minBits := tableLog + 1 - maxW in
        let! rv := rank_val_rows (Z.to_nat (Z.max 0 (maxTableLog - minBits + 1 - minBits))) minBits maxW rv0 in
        let! cells := fill_x2 (Z.to_nat (maxW + 1)) (repeat None (Z.to_nat ncells)) 1 (maxW + 1) maxTableLog rv sorted rs0 (tableLog + 1) in
        Ok (maxTableLog, cells, hs_ret h).
End TableX2.

Definition x2_cells (cells : list (option deltX2)) : list deltX2 :=
  map (fun o => match o with Some c => c | None => x2_default end) cells.

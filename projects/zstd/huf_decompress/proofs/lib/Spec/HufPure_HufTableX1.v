(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_FseDecomp HufPure_HufStats HufPure_HufX1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition HUF_DECODER_FAST_TABLELOG : Z := 11.
(* [comment removed for export] *)
Definition X1_WKSP_SIZE : Z := (13 + 13 + 219) * 4 + 256 + 256.

(* [comment removed for export] *)
Definition ostoreX (l : list (option deltX1)) (i : Z) (v : deltX1) : res (list (option deltX1)) :=
  if (0 <=? i) && (i <? Zlength l) then
    Ok (firstn (Z.to_nat i) l ++ Some v :: skipn (S (Z.to_nat i)) l)
  else Ub.

Section TableX1.
  Variable L : Z.              (* [comment removed for export] *)
  Variable src : list Z.
  Variable wkspSize : Z.
  Let ncells : Z := 2^(L + 1).

  (* [comment removed for export] *)
  Fixpoint shift_rank (fuel : nat) (s scale : Z) (rank : list Z) : res (list Z) :=
    match fuel with
    | O => Ok rank
    | S f =>   (* [comment removed for export] *)
      let! v := load rank (s - scale) in
      let! rank' := store rank s v in
      shift_rank f (s - 1) scale rank'
    end.
  Fixpoint zero_rank (fuel : nat) (s : Z) (rank : list Z) : res (list Z) :=
    match fuel with
    | O => Ok rank
    | S f =>   (* [comment removed for export] *)
      let! rank' := store rank s 0 in
      zero_rank f (s - 1) rank'
    end.

  Definition rescale (ws : list Z) (rank : list Z) (nbSymbols tableLog target : Z) : res (list Z * list Z * Z) :=
    if target <? tableLog then Ok (ws, rank, tableLog)
    else if tableLog <? target then
      let scale := target - tableLog in
      (* [comment removed for export] *)
      let! _ := assert (nbSymbols <=? Zlength ws) in
      let ws' := map (fun w => if w =? 0 then w else to_byte (w + scale)) (firstn (Z.to_nat nbSymbols) ws)
                 ++ skipn (Z.to_nat nbSymbols) ws in
      let! rank1 := shift_rank (Z.to_nat (target - scale)) target scale rank in
      let! rank2 := zero_rank (Z.to_nat scale) scale rank1 in
      Ok (ws', rank2, target)
    else Ok (ws, rank, target).

  (* [comment removed for export] *)
  Fixpoint rank_start_loop (fuel : nat) (n : Z) (next : Z) (rank : list Z) (rs : list Z) : res (list Z) :=
    match fuel with
    | O => Ok rs
    | S f =>
      let! v := load rank n in
      let! rs' := store rs n next in
      rank_start_loop f (n + 1) (u32 (next + v)) rank rs'
    end.

  (* [comment removed for export] *)
  Fixpoint sort_loop (fuel : nat) (n : Z) (ws : list Z) (rs : list Z) (syms : list (option Z)) : res (list Z * list (option Z)) :=
    match fuel with
    | O => Ok (rs, syms)
    | S f =>
      let! w := load ws n in
      let! p := load rs w in
      let! rs' := store rs w (u32 (p + 1)) in
      let! syms' := ostore syms p n in
      sort_loop f (n + 1) ws rs' syms'
    end.

  (* [comment removed for export] *)
  Fixpoint fill_cells (k : nat) (cells : list (option deltX1)) (u : Z) (c : deltX1) : res (list (option deltX1)) :=
    match k with
    | O => Ok cells
    | S k' => let! cells' := ostoreX cells u c in fill_cells k' cells' (u + 1) c
    end.

  Fixpoint fill_syms (fuel : nat) (s symbolCount symbol : Z) (length nbBits : Z) (syms : list (option Z))
           (cells : list (option deltX1)) (uStart : Z) : res (list (option deltX1) * Z) :=
    match fuel with
    | O => Ok (cells, uStart)
    | S f =>
      if s <? symbolCount then
        let! b := oload syms (symbol + s) in
        let! cells' := fill_cells (Z.to_nat length) cells uStart (mkX1 nbBits b) in
        fill_syms f (s + 1) symbolCount symbol length nbBits syms cells' (uStart + length)
      else Ok (cells, uStart)
    end.

  Fixpoint fill_weights (fuel : nat) (w tableLog : Z) (rank : list Z) (syms : list (option Z))
           (cells : list (option deltX1)) (symbol rankStart : Z) : res (list (option deltX1)) :=
    match fuel with
    | O => Ok cells
    | S f =>
      let! symbolCount := load rank w in
      let! p := shl32 1 w in
      let length := p / 2 in
      let nbBits := to_byte (tableLog + 1 - w) in
      let! r := fill_syms (S (Z.to_nat symbolCount)) 0 symbolCount symbol length nbBits syms cells rankStart in
      let '(cells', _) := r in
      fill_weights f (w + 1) tableLog rank syms cells' (symbol + symbolCount) (rankStart + symbolCount * length)
    end.

  (* [comment removed for export] *)
  Definition read_dtable_x1 : res (Z * list (option deltX1) * Z) :=
    if wkspSize <? X1_WKSP_SIZE then Err ZSTD_error_tableLog_tooLarge
    else
      let! h := read_stats src in
      let maxTableLog := L + 1 in
      let target := Z.min maxTableLog HUF_DECODER_FAST_TABLELOG in
      let! rsc := rescale (hs_weights h) (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) target in
      let '(ws, rank, tableLog) := rsc in
      if maxTableLog <? tableLog then Err ZSTD_error_tableLog_tooLarge
      else
        let! rs := rank_start_loop (Z.to_nat (tableLog + 1)) 0 0 rank (repeat 0 13) in
        let! sr := sort_loop (Z.to_nat (hs_nbSymbols h)) 0 ws rs (repeat None 256) in
        let '(_, syms) := sr in
        let! symbol0 := load rank 0 in
        let! cells := fill_weights (Z.to_nat tableLog) 1 tableLog rank syms (repeat None (Z.to_nat ncells)) symbol0 0 in
        Ok (tableLog, cells, hs_ret h).
End TableX1.

(* [comment removed for export] *)
Definition x1_cells (cells : list (option deltX1)) : list deltX1 :=
  map (fun o => match o with Some c => c | None => x1_default end) cells.

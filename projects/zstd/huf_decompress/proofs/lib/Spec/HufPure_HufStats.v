(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_FseDecomp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition HUF_TABLELOG_MAX : Z := 12.
Definition HUF_SYMBOLVALUE_MAX : Z := 255.

Record hstats := mkHS {
  hs_weights : list Z;     (* [comment removed for export] *)
  hs_rank : list Z;        (* [comment removed for export] *)
  hs_nbSymbols : Z;
  hs_tableLog : Z;
  hs_ret : Z               (* [comment removed for export] *)
}.

Section Stats.
  Variable src : list Z.
  Let srcSize : Z := Zlength src.
  Let hwSize : Z := HUF_SYMBOLVALUE_MAX + 1.

  (* [comment removed for export] *)
  Fixpoint direct_loop (fuel : nat) (n oSize : Z) (acc : list Z) : res (list Z) :=
    match fuel with
    | O => NoFuel
    | S f =>
      if n <? oSize then
        let! b := load src (1 + n / 2) in
        let! _ := assert (n + 1 <? hwSize) in          (* [comment removed for export] *)
        direct_loop f (n + 2) oSize (acc ++ [b / 16; Z.land b 15])
      else Ok acc
    end.

  (* [comment removed for export] *)
  Fixpoint collect_loop (ws : list Z) (rank : list Z) (weightTotal : Z) : res (list Z * Z) :=
    match ws with
    | [] => Ok (rank, weightTotal)
    | w :: ws' =>
      if HUF_TABLELOG_MAX <? w then Err ZSTD_error_corruption_detected
      else
        let! r := load rank w in
        let! rank' := store rank w (u32 (r + 1)) in
        let! p := shl32 1 w in
        collect_loop ws' rank' (u32 (weightTotal + p / 2))
    end.

  Definition read_stats : res hstats :=
    if srcSize =? 0 then Err ZSTD_error_srcSize_wrong
    else
      let! iSize := load src 0 in
      let! hdr :=
        (if 128 <=? iSize then
           let oSize := iSize - 127 in
           let iSize' := (oSize + 1) / 2 in
           if srcSize <? iSize' + 1 then Err ZSTD_error_srcSize_wrong
           else if hwSize <=? oSize then Err ZSTD_error_corruption_detected
           else
             let! cells := direct_loop (S (Z.to_nat oSize)) 0 oSize [] in
             Ok (firstn (Z.to_nat oSize) cells, oSize, iSize')
         else
           if srcSize <? iSize + 1 then Err ZSTD_error_srcSize_wrong
           else
             let! ws := huf_fse_weights (firstn (Z.to_nat iSize) (skipn 1 src)) in
             Ok (ws, Zlength ws, iSize)) in
      let '(ws, oSize, iSize') := hdr in
      (* [comment removed for export] *)
      let rank0 := repeat 0 (Z.to_nat (HUF_TABLELOG_MAX + 1)) in
      let! cr := collect_loop ws rank0 0 in
      let '(rank1, weightTotal) := cr in
      if weightTotal =? 0 then Err ZSTD_error_corruption_detected
      else
        let! hb := highbit32 weightTotal in
        let tableLog := hb + 1 in
        if HUF_TABLELOG_MAX <? tableLog then Err ZSTD_error_corruption_detected
        else
          let! total := shl32 1 tableLog in
          let rest := u32 (total - weightTotal) in
          let! hr := highbit32 rest in
          let! verif := shl32 1 hr in
          let lastWeight := hr + 1 in
          if negb (verif =? rest) then Err ZSTD_error_corruption_detected
          else
            let! _ := assert (oSize <? hwSize) in                 (* [comment removed for export] *)
            let! r := load rank1 lastWeight in
            let! rank2 := store rank1 lastWeight (u32 (r + 1)) in
            let! r1 := load rank2 1 in
            if (r1 <? 2) || (Z.land r1 1 =? 1) then Err ZSTD_error_corruption_detected
            else Ok (mkHS (ws ++ [lastWeight]) rank2 (u32 (oSize + 1)) tableLog (iSize' + 1)).
End Stats.

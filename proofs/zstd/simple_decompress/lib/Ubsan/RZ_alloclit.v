(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdLit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface RZ_blk_iface4 seqH_kit seqH_kit_lit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem zd_alloclit_proof : zd_alloclit_stmt.
Proof.
  unfold zd_alloclit_stmt, PZD_ALLOCLIT. intros until ws.
  intros FP BSM (H5 & L5) ISF DCL DCH DST0 CAP0 DSTH DNZ DAL LSZ EWS SPR MI -> -> -> -> -> -> ->.
  assert (MU : munch [(DCTX + DCTX_litBuffer, DCTX + DCTX_litBuffer + 20)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  unfold zfh_cells in FP. unfold DCTX_litBuffer in MU.
  h5_open ws L5. lazymatch type of ISF with ?x = _ => subst x end.
  zstep. uck. zstep. zstep. uck. zstep. zstep. zstep. zstep. rewrite (sx32w_small 1) by lia.
  zstep. if_false.
  zstep. zstep. if_false. zstep.
  rewrite (zx32w_small (fh_bsmax h)) by lia.
  zstep. zstep. zstep. if_cases K2; zify_cond K2.
  - zstep. zstep. if_cases K3; zify_cond K3.
    + (* [comment removed for export] *)
      zstep. if_cases K4; zify_cond K4.
      * (* [comment removed for export] *)
        destruct imm; [exfalso; cbn in K4; lia|].
        zstep. zstep. uck. zstep. zstep. zstep. zstep. uckb. zstep. uck. zstep. zstep. zstep. zstep. uckb.
        zstep. zstep. zstep. zstep. zstep. zstep.
        apply evt_done. unfold zd_alloclit_post. do 15 eexists. eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
        split; [|reflexivity].
        unfold alloc_lit_buffer, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE.
        replace (fh_bsmax h + 32 + litSize + 32 <? CAP) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (litSize <=? 65536) with false by (symmetry; apply Z.leb_gt; lia).
        cbv [h5_placed h5_cells mk_wcells h5_sizes wupd lp_loc lp_base lp_buf lp_end lit_base_addr H5_litBuffer H5_litBufferEnd H5_litBufferLocation ZSTD_split].
        lazymatch type of H5 with rw_cells _ _ _ ?cs => lazymatch goal with |- rw_cells _ _ _ ?cg => replace cg with cs; [exact H5|] end end.
        repeat (f_equal; try lia).
      * (* [comment removed for export] *)
        destruct imm; [|exfalso; cbn in K4; lia].
        zstep. zstep. uck. zstep. zstep. zstep. zstep. uckb. zstep. uck. zstep. zstep. zstep. zstep. uckb.
        zstep. zstep. zstep. zstep. uck. zstep. zstep. zstep. zstep. uck. zstep. uck.
        zstep. zstep. zstep. zstep. zstep. uckb. zstep. zstep. zstep. uck. zstep. zstep. uckb.
        zstep. zstep. zstep. zstep. zstep. zstep.
        apply evt_done. unfold zd_alloclit_post. do 15 eexists. eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
        split; [|reflexivity].
        unfold alloc_lit_buffer, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE.
        replace (fh_bsmax h + 32 + litSize + 32 <? CAP) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (litSize <=? 65536) with false by (symmetry; apply Z.leb_gt; lia).
        cbv [h5_placed h5_cells mk_wcells h5_sizes wupd lp_loc lp_base lp_buf lp_end lit_base_addr H5_litBuffer H5_litBufferEnd H5_litBufferLocation ZSTD_split].
        lazymatch type of H5 with rw_cells _ _ _ ?cs => lazymatch goal with |- rw_cells _ _ _ ?cg => replace cg with cs; [exact H5|] end end.
        repeat (f_equal; try lia).
    + (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. uckb. zstep. zstep. zstep. zstep.
      apply evt_done. unfold zd_alloclit_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [|reflexivity].
      unfold alloc_lit_buffer, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE.
      replace (fh_bsmax h + 32 + litSize + 32 <? CAP) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (litSize <=? 65536) with true by (symmetry; apply Z.leb_le; lia).
      cbv [h5_placed h5_cells mk_wcells h5_sizes wupd lp_loc lp_base lp_buf lp_end lit_base_addr H5_litBuffer H5_litBufferEnd H5_litBufferLocation ZSTD_not_in_dst DCTX_litExtraBuffer].
      lazymatch type of H5 with rw_cells _ _ _ ?cs => lazymatch goal with |- rw_cells _ _ _ ?cg => replace cg with cs; [exact H5|] end end.
      repeat (f_equal; try lia).
  - (* [comment removed for export] *)
    zstep. zstep. uck. zstep. zstep. zstep. zstep. uckb. zstep. uck. zstep. zstep. uck.
    zstep. zstep. zstep. zstep. uckb. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. unfold zd_alloclit_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [|reflexivity].
    unfold alloc_lit_buffer, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE.
    replace (fh_bsmax h + 32 + litSize + 32 <? CAP) with true by (symmetry; apply Z.ltb_lt; lia).
    cbv [h5_placed h5_cells mk_wcells h5_sizes wupd lp_loc lp_base lp_buf lp_end lit_base_addr H5_litBuffer H5_litBufferEnd H5_litBufferLocation ZSTD_in_dst].
    lazymatch type of H5 with rw_cells _ _ _ ?cs => lazymatch goal with |- rw_cells _ _ _ ?cg => replace cg with cs; [exact H5|] end end.
    repeat (f_equal; try lia).
Qed.

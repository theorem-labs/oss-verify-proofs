(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_pure RF_huf_fdw_fm RF_huf_fdw_st.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_bdt_model.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AProg_kit ABytes AKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fdw_seg AF_huf_fdw_top1 AF_huf_reloadi.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.

Section FTB.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (m0 : amem) (SPV FF DST dcap S0 DT lo RLO RHI : Z) (bs : list Z)
            (d : dtable) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (j48 jd : list byte).
  Notation SP1 := (SPAf SPV).
  Notation tl := (dt_tableLog d).
  Notation TB := (DT + 4).
  Notation TBC := (concat (map fse_cell_bytes (dt_cells d))).
  Notation FRC := [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 2147450880)].
  Notation W0 := [(lo, SP1); (SP1 + 80, SP1 + 152); (DST, DST + dcap)].

  Definition ftA_inv (mm : amem) (x : dec) (jp junk : list byte) : Prop :=
    munch W0 m0 mm /\ wmono bsegs m0 mm /\ mem_inv bsegs mm /\ stk bsegs mm lo SP1 /\ artcells mm /\
    rw_cells bsegs mm (SP1 + 32) FRC /\
    rw_cells bsegs mm (SP1 + 80) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 TB); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 TB)] /\
    rw_cells bsegs mm (SP1 + 112) (bitdz_cellsA S0 (de_bd x) jp) /\
    u8arr bsegs mm DST (map (Z_to_bv 8) (de_out x) ++ junk) /\ zlen junk = dcap - zlen (de_out x) /\
    bytes_at bsegs mm S0 (map (Z_to_bv 8) bs) /\ bytes_at bsegs mm TB TBC /\
    zshadow mm (SP1 + 80) 72 /\ zshadow mm DT (4 + 4 * 2^tl) /\ zshadow mm DST dcap /\ zshadow mm ABIT_MASK 128 /\
    (0 < zlen bs -> unpoisoned mm S0 (S0 + zlen bs)).

  Notation R := (decompress_usingDTable bs d dcap true).
  Notation FN pc mm j i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SP1)
             x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x19 (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
             x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Definition ftA_f1_stmt : Prop :=
    forall x mm jp junk (j i : Z) (st : dstatus) (d1r : bitD)
           (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
      reload_dstream bs (de_bd x) = Ok (st, d1r) -> 64 < bd_bits (de_bd x) -> bitd_ok bs (de_bd x) ->
      zlen (de_out x) = j + i + 1 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
      ftA_inv mm x jp junk ->
      R = (let! q := decode_sym d true (de_s2 x) d1r in let '(o1, _, _) := q in Ok (de_out x ++ [o1])) ->
      evtF bsegs RNG Q (FN 0x99bc8 mm j i y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31).

  Definition ftA_f2_stmt : Prop :=
    forall x mm jp junk (j i : Z) (st : dstatus) (d2r : bitD)
           (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
      reload_dstream bs (de_bd x) = Ok (st, d2r) -> 64 < bd_bits (de_bd x) -> bitd_ok bs (de_bd x) ->
      zlen (de_out x) = j + i + 2 -> zlen (de_out x) <= dcap - 1 -> 0 <= j -> 0 <= i ->
      ftA_inv mm x jp junk ->
      R = (let! q := decode_sym d true (de_s1 x) d2r in let '(o2, _, _) := q in Ok (de_out x ++ [o2])) ->
      evtF bsegs RNG Q (FN 0x99c04 mm j i y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y24 y25 y26 y28 y29 y30 y31).
End FTB.

End CANSEC1.

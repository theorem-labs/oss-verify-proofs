(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record ssp : Type := mkSSP {
  v_ra : word;
  v_gp : word;
  v_tp : word;
  v_s0 : word;
  v_s1 : word;
  v_s2 : word;
  v_s3 : word;
  v_s4 : word;
  v_s5 : word;
  v_s6 : word;
  v_s7 : word;
  v_s8 : word;
  v_s9 : word;
  v_s10 : word;
  v_s11 : word;
  v_F : bvmap 5 word;
  v_fc : bv 32;
  v_m : fmem;
  v_SPV : Z;
  v_lo : Z;
  v_DCTX : Z;
  v_DST : Z;
  v_CAP : Z;
  v_B0 : Z;
  v_B1 : Z;
  v_SEQ : Z;
  v_nbSeq : Z;
  v_LLT : Z;
  v_MLT : Z;
  v_OFT : Z;
  v_PFX : Z;
  v_LITP : Z;
  v_LBE : Z;
  v_LITB : Z;
  v_LOC : Z;
  v_sq : list Z;
  v_tLL : seq_table;
  v_tOF : seq_table;
  v_tML : seq_table;
  v_huf : word;
  v_r0 : word;
  v_r1 : word;
  v_r2 : word;
  v_pde : word;
  v_dend : word;
  v_expd : word;
  v_pcs : word;
  v_dsz : word;
  v_bt : word;
  v_stg : word;
  v_le : word;
  v_fe : word;
  v_ws : list word }.

(* [comment removed for export] *)
Definition seqs_mem (P : ssp) : Prop := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  seq_dctx m DCTX LLT MLT OFT huf r0 r1 r2 pde PFX PFX dend expd pcs dsz bt stg le fe ws /\ seq_lit2 ws LITP LBE LITB LOC /\
  bytes_at usegs m SEQ (map (Z_to_bv 8) sq) /\ stk usegs m B0 B1 /\
  rdbl usegs m LITP (LBE + WILDCOPY_OVERLENGTH) /\ stk usegs m lo SPV /\ mem_inv usegs m.
Definition seqs_ranges (P : ssp) : Prop := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  4096 <= DCTX /\ DCTX + DCTX_SIZEOF < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 0 <= nbSeq <= 98047 /\
  4096 <= B0 /\ B0 <= DST /\ DST + CAP <= B1 /\ 0 <= CAP /\ B1 < 2^47 /\
  4096 <= LITP /\ LITP <= LBE /\ LBE + WILDCOPY_OVERLENGTH < 2^47 /\
  lo <= SPV - SEQ_SPLIT_STACK /\ 0 <= SPV < 2^47 /\ 4096 <= lo.
Definition seqs_side (P : ssp) : Prop := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  DCTX mod 8 = 0 /\ all_bytes sq /\ (nbSeq <> 0 -> B0 <= PFX <= DST) /\ (LOC = ZSTD_split) /\
  seq_lit_placed m DCTX DST CAP B0 B1 LITP LBE LITB LOC.
Definition seqs_sep (P : ssp) : Prop := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  off_stack lo SPV DCTX DCTX_SIZEOF /\ off_stack lo SPV B0 (B1 - B0) /\ off_stack lo SPV SEQ (zlen sq) /\
  off_stack lo SPV LITP (LBE + WILDCOPY_OVERLENGTH - LITP) /\
  apart B0 (B1 - B0) DCTX DCTX_SIZEOF /\ apart B0 (B1 - B0) SEQ (zlen sq) /\
  apart SEQ (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  (LOC <> ZSTD_split -> apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep)).
Definition seqs_tables (P : ssp) : Prop := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  seq_table_at m K_LL LLT tLL /\ seq_table_at m K_OF OFT tOF /\ seq_table_at m K_ML MLT tML /\
  4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47 /\
  off_stack lo SPV LLT (8 * (1 + 2^9)) /\ off_stack lo SPV OFT (8 * (1 + 2^8)) /\ off_stack lo SPV MLT (8 * (1 + 2^9)) /\
  apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ apart B0 (B1 - B0) MLT (8 * (1 + 2^9)) /\
  apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  (LLT mod 4 = 0 /\ OFT mod 4 = 0 /\ MLT mod 4 = 0 /\ SPV mod 16 = 0).

Definition seqs_post (P : ssp) : machine_state -> Prop := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  zd_seq_split_post SEQ_SPLIT_STACK ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 nbSeq pcs dsz bt stg le fe ws lo m.

(* [comment removed for export] *)
Definition seqs_saved (P : ssp) : list cell := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition seqs_xinv (P : ssp) (m1 : fmem) (fe' : word) : Prop := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  (exists r0' r1' r2', rw_cells usegs m1 (DCTX + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) /\
  dctx_h3 usegs m1 DCTX pcs dsz bt stg le fe' /\
  stk usegs m1 B0 B1 /\ stk usegs m1 lo (SPV + -384) /\
  munch [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
         (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4);
         (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4); (SPV - SEQ_SPLIT_STACK, SPV)] m m1 /\
  wmono usegs m m1 /\ mem_inv usegs m1.

(* [comment removed for export] *)
Definition seqs_fe (P : ssp) : word := if v_nbSeq P =? 0 then v_fe P else Z_to_bv 64 1.

(* [comment removed for export] *)
Lemma seqs_p_exit : forall (P : ssp) m1 jpre r loc (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqs_ranges P -> seqs_xinv P m1 (seqs_fe P) -> h5_viewed m1 (v_DCTX P) (v_ws P) loc ->
  rw_cells usegs m1 (v_SPV P + -384) (CB 280 jpre :: seqs_saved P) ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= v_CAP P) ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 r) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c6fc) (v_fc P) None m1 (seg_rom usegs)).
Proof.
  intros [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws] m1 jpre r loc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 RG XI H5V FR RR RES.
  unfold seqs_fe in *. cbn [seqs_ranges seqs_xinv seqs_post seqs_saved v_SPV v_gp v_tp v_F v_fc v_CAP v_nbSeq v_fe v_DCTX v_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct XI as ((r0' & r1' & r2' & REP) & H3 & BUF & STK & MU & WM & MI1).
  apply h5_close in H5V.
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  clear G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13. hold REP. hold H3. hold BUF. hold H5V.
  kx_run [] 20%nat [KZRange SPV 592 (2^47)] [].
  unfold held in *.
  release_frame FR STK SPV.
  zstep.
  apply evt_done. unfold zd_seq_split_post.
  do 15 eexists. exists r, r0', r1', r2', (wupd ws H5_litBufferLocation loc).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact STK|]. split; [exact BUF|].
  split; [exact REP|]. split; [exact H3|]. split; [exact H5V|].
  split; [intros i Hi; apply wnth_wupd_other; exact Hi|]. split; [exact RR| exact RES].
Qed.

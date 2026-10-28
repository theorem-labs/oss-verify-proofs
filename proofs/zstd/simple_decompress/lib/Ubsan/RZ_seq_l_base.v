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

Record slp : Type := mkSLP {
  y_ra : word;
  y_gp : word;
  y_tp : word;
  y_s0 : word;
  y_s1 : word;
  y_s2 : word;
  y_s3 : word;
  y_s4 : word;
  y_s5 : word;
  y_s6 : word;
  y_s7 : word;
  y_s8 : word;
  y_s9 : word;
  y_s10 : word;
  y_s11 : word;
  y_F : bvmap 5 word;
  y_fc : bv 32;
  y_m : fmem;
  y_SPV : Z;
  y_lo : Z;
  y_DCTX : Z;
  y_DST : Z;
  y_CAP : Z;
  y_B0 : Z;
  y_B1 : Z;
  y_SEQ : Z;
  y_nbSeq : Z;
  y_LLT : Z;
  y_MLT : Z;
  y_OFT : Z;
  y_PFX : Z;
  y_LITP : Z;
  y_LBE : Z;
  y_LITB : Z;
  y_LOC : Z;
  y_sq : list Z;
  y_tLL : seq_table;
  y_tOF : seq_table;
  y_tML : seq_table;
  y_huf : word;
  y_r0 : word;
  y_r1 : word;
  y_r2 : word;
  y_pde : word;
  y_dend : word;
  y_expd : word;
  y_pcs : word;
  y_dsz : word;
  y_bt : word;
  y_stg : word;
  y_le : word;
  y_fe : word;
  y_ws : list word }.

(* [comment removed for export] *)
Definition seql_mem (P : slp) : Prop := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  seq_dctx m DCTX LLT MLT OFT huf r0 r1 r2 pde PFX PFX dend expd pcs dsz bt stg le fe ws /\ seq_lit2 ws LITP LBE LITB LOC /\
  bytes_at usegs m SEQ (map (Z_to_bv 8) sq) /\ stk usegs m B0 B1 /\
  rdbl usegs m LITP (LBE + WILDCOPY_OVERLENGTH) /\ stk usegs m lo SPV /\ mem_inv usegs m.
Definition seql_ranges (P : slp) : Prop := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  4096 <= DCTX /\ DCTX + DCTX_SIZEOF < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 0 <= nbSeq <= 98047 /\
  4096 <= B0 /\ B0 <= DST /\ DST + CAP <= B1 /\ 0 <= CAP /\ B1 < 2^47 /\
  4096 <= LITP /\ LITP <= LBE /\ LBE + WILDCOPY_OVERLENGTH < 2^47 /\
  lo <= SPV - SEQ_LONG_STACK /\ 0 <= SPV < 2^47 /\ 4096 <= lo.
Definition seql_side (P : slp) : Prop := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  DCTX mod 8 = 0 /\ all_bytes sq /\ (nbSeq <> 0 -> B0 <= PFX <= DST) /\ (LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst \/ LOC = ZSTD_split) /\
  seq_lit_placed m DCTX DST CAP B0 B1 LITP LBE LITB LOC.
Definition seql_sep (P : slp) : Prop := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  off_stack lo SPV DCTX DCTX_SIZEOF /\ off_stack lo SPV B0 (B1 - B0) /\ off_stack lo SPV SEQ (zlen sq) /\
  off_stack lo SPV LITP (LBE + WILDCOPY_OVERLENGTH - LITP) /\
  apart B0 (B1 - B0) DCTX DCTX_SIZEOF /\ apart B0 (B1 - B0) SEQ (zlen sq) /\
  apart SEQ (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  (LOC <> ZSTD_split -> apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep)).
Definition seql_tables (P : slp) : Prop := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  seq_table_at m K_LL LLT tLL /\ seq_table_at m K_OF OFT tOF /\ seq_table_at m K_ML MLT tML /\
  4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47 /\
  off_stack lo SPV LLT (8 * (1 + 2^9)) /\ off_stack lo SPV OFT (8 * (1 + 2^8)) /\ off_stack lo SPV MLT (8 * (1 + 2^9)) /\
  apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ apart B0 (B1 - B0) MLT (8 * (1 + 2^9)) /\
  apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  (LLT mod 4 = 0 /\ OFT mod 4 = 0 /\ MLT mod 4 = 0 /\ SPV mod 16 = 0).

Definition seql_post (P : slp) : machine_state -> Prop := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  zd_seq_split_post SEQ_LONG_STACK ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 nbSeq pcs dsz bt stg le fe ws lo m.

(* [comment removed for export] *)
Definition seql_saved (P : slp) : list cell := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition seql_xinv (P : slp) (m1 : fmem) (fe' : word) : Prop := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  (exists r0' r1' r2', rw_cells usegs m1 (DCTX + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) /\
  dctx_h3 usegs m1 DCTX pcs dsz bt stg le fe' /\
  stk usegs m1 B0 B1 /\ stk usegs m1 lo (SPV + -688) /\
  munch [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
         (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4);
         (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4); (SPV - SEQ_LONG_STACK, SPV)] m m1 /\
  wmono usegs m m1 /\ mem_inv usegs m1.

(* [comment removed for export] *)
Definition seql_fe (P : slp) : word := if y_nbSeq P =? 0 then y_fe P else Z_to_bv 64 1.

(* [comment removed for export] *)
Lemma seql_p_exit : forall (P : slp) m1 jpre r loc (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seql_ranges P -> seql_xinv P m1 (seql_fe P) -> h5_viewed m1 (y_DCTX P) (y_ws P) loc ->
  rw_cells usegs m1 (y_SPV P + -688) (CB 584 jpre :: seql_saved P) ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= y_CAP P) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1abb4) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  intros [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws] m1 jpre r loc x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 RG XI H5V FR RR RES.
  unfold seql_fe in *. cbn [seql_ranges seql_xinv seql_post seql_saved y_SPV y_gp y_tp y_F y_fc y_CAP y_nbSeq y_fe y_DCTX y_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct XI as ((r0' & r1' & r2' & REP) & H3 & BUF & STK & MU & WM & MI1).
  apply h5_close in H5V.
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  clear G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13. hold REP. hold H3. hold BUF. hold H5V.
  kx_run [] 20%nat [KZRange SPV 896 (2^47)] [].
  unfold held in *.
  release_frame FR STK SPV.
  zstep.
  apply evt_done. unfold zd_seq_split_post.
  do 15 eexists. exists r, r0', r1', r2', (wupd ws H5_litBufferLocation loc).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact STK|]. split; [exact BUF|].
  split; [exact REP|]. split; [exact H3|]. split; [exact H5V|].
  split; [intros i Hi; apply wnth_wupd_other; exact Hi|]. split; [exact RR| exact RES].
Qed.

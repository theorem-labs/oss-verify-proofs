(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record sdp : Type := mkSDP {
  q_ra : word;
  q_gp : word;
  q_tp : word;
  q_s0 : word;
  q_s1 : word;
  q_s2 : word;
  q_s3 : word;
  q_s4 : word;
  q_s5 : word;
  q_s6 : word;
  q_s7 : word;
  q_s8 : word;
  q_s9 : word;
  q_s10 : word;
  q_s11 : word;
  q_F : bvmap 5 word;
  q_fc : bv 32;
  q_m : fmem;
  q_SPV : Z;
  q_lo : Z;
  q_DCTX : Z;
  q_DST : Z;
  q_CAP : Z;
  q_B0 : Z;
  q_B1 : Z;
  q_SEQ : Z;
  q_nbSeq : Z;
  q_LLT : Z;
  q_MLT : Z;
  q_OFT : Z;
  q_PFX : Z;
  q_LITP : Z;
  q_LITSZ : Z;
  q_LITB : Z;
  q_LOC : Z;
  q_sq : list Z;
  q_tLL : seq_table;
  q_tOF : seq_table;
  q_tML : seq_table;
  q_huf : word;
  q_r0 : word;
  q_r1 : word;
  q_r2 : word;
  q_pde : word;
  q_dend : word;
  q_expd : word;
  q_pcs : word;
  q_dsz : word;
  q_bt : word;
  q_stg : word;
  q_le : word;
  q_fe : word;
  q_ws : list word }.

(* [comment removed for export] *)
Definition seqd_mem (P : sdp) : Prop := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  seq_dctx m DCTX LLT MLT OFT huf r0 r1 r2 pde PFX PFX dend expd pcs dsz bt stg le fe ws /\ seq_lit ws LITP LITSZ LITB LOC /\
  bytes_at usegs m SEQ (map (Z_to_bv 8) sq) /\ stk usegs m B0 B1 /\
  rdbl usegs m LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH) /\ stk usegs m lo SPV /\ mem_inv usegs m.
Definition seqd_ranges (P : sdp) : Prop := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  4096 <= DCTX /\ DCTX + DCTX_SIZEOF < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 0 <= nbSeq <= 98047 /\
  B0 <= DST /\ DST + CAP <= B1 /\ 0 <= CAP /\ B1 < 2^47 /\
  0 <= LITSZ < 2^32 /\ 4096 <= LITP /\ LITP + LITSZ + WILDCOPY_OVERLENGTH < 2^47 /\
  lo <= SPV - SEQ_STACK /\ 0 <= SPV < 2^47 /\ 4096 <= lo.
Definition seqd_side (P : sdp) : Prop := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  DCTX mod 8 = 0 /\ all_bytes sq /\ (DST = 0 -> CAP = 0 /\ nbSeq = 0) /\ (DST <> 0 -> 4096 <= B0) /\ (nbSeq <> 0 -> B0 <= PFX <= DST) /\
  (LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst) /\
  (LOC = ZSTD_in_dst -> DST <= LITB <= DST + CAP /\ LITB <= LITP /\ LITP + LITSZ + WILDCOPY_OVERLENGTH <= B1) /\
  (LOC = ZSTD_not_in_dst -> apart LITP (LITSZ + WILDCOPY_OVERLENGTH) B0 (B1 - B0)).
Definition seqd_sep (P : sdp) : Prop := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  off_stack lo SPV DCTX DCTX_SIZEOF /\ off_stack lo SPV B0 (B1 - B0) /\ off_stack lo SPV SEQ (zlen sq) /\
  off_stack lo SPV LITP (LITSZ + WILDCOPY_OVERLENGTH) /\
  apart B0 (B1 - B0) DCTX DCTX_SIZEOF /\ apart B0 (B1 - B0) SEQ (zlen sq) /\
  apart SEQ (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart LITP (LITSZ + WILDCOPY_OVERLENGTH) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep).
Definition seqd_tables (P : sdp) : Prop := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  seq_table_at m K_LL LLT tLL /\ seq_table_at m K_OF OFT tOF /\ seq_table_at m K_ML MLT tML /\
  4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47 /\
  off_stack lo SPV LLT (8 * (1 + 2^9)) /\ off_stack lo SPV OFT (8 * (1 + 2^8)) /\ off_stack lo SPV MLT (8 * (1 + 2^9)) /\
  apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ apart B0 (B1 - B0) MLT (8 * (1 + 2^9)) /\
  apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep).

Definition seqd_post (P : sdp) : machine_state -> Prop := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  zd_seq_default_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 nbSeq pcs dsz bt stg le fe lo m.

(* [comment removed for export] *)
Definition seqd_saved (P : sdp) : list cell := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition seqd_xinv (P : sdp) (m1 : fmem) (fe' : word) : Prop := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  (exists r0' r1' r2', rw_cells usegs m1 (DCTX + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) /\
  dctx_h3 usegs m1 DCTX pcs dsz bt stg le fe' /\
  stk usegs m1 B0 B1 /\ stk usegs m1 lo (SPV + -352) /\
  munch [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
         (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (SPV - SEQ_STACK, SPV)] m m1 /\
  wmono usegs m m1 /\ mem_inv usegs m1.

(* [comment removed for export] *)
Definition seqd_fe (P : sdp) : word := if q_nbSeq P =? 0 then q_fe P else Z_to_bv 64 1.

(* [comment removed for export] *)
Lemma p_exit : forall (P : sdp) m1 jpre r (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seqd_ranges P -> seqd_xinv P m1 (seqd_fe P) ->
  rw_cells usegs m1 (q_SPV P + -352) (CB 248 jpre :: seqd_saved P) ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= q_CAP P) ->
  evt usegs (seqd_post P)
    (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31)
        (q_F P) (Z_to_bv 64 0x1d6e4) (q_fc P) None m1 (seg_rom usegs)).
Proof.
  intros [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws] m1 jpre r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 RG XI FR RR RES.
  unfold seqd_fe in *. cbn [seqd_ranges seqd_xinv seqd_post seqd_saved q_SPV q_gp q_tp q_F q_fc q_CAP q_nbSeq q_fe] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  destruct XI as ((r0' & r1' & r2' & REP) & H3 & BUF & STK & MU & WM & MI1).
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy in *.
  clear G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12. hold REP. hold H3. hold BUF.
  kx_run [] 20%nat [KZRange SPV 544 (2^47)] [].
  unfold held in *.
  release_frame FR STK SPV.
  zstep.
  apply evt_done. unfold zd_seq_default_post.
  do 15 eexists. exists r, r0', r1', r2'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact STK|]. split; [exact BUF|].
  split; [exact REP|]. split; [exact H3|]. split; [exact RR| exact RES].
Qed.

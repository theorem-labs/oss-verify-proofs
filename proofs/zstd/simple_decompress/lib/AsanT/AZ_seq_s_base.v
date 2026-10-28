(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Record ssq : Type := mkSSQ {
  v_ra : word; v_gp : word; v_tp : word;
  v_s0 : word; v_s1 : word; v_s2 : word; v_s3 : word; v_s4 : word; v_s5 : word; v_s6 : word; v_s7 : word; v_s8 : word;
  v_s9 : word; v_s10 : word; v_s11 : word;
  v_F : bvmap 5 word; v_fc : bv 32;
  v_m : amem;
  v_SPV : Z; v_lo : Z; v_DCTX : Z; v_DST : Z; v_CAP : Z; v_B0 : Z; v_B1 : Z; v_SEQ : Z; v_nbSeq : Z;
  v_LLT : Z; v_MLT : Z; v_OFT : Z; v_PFX : Z; v_LITP : Z; v_LBE : Z; v_LITB : Z; v_LOC : Z;
  v_sq : list Z; v_tLL : seq_table; v_tOF : seq_table; v_tML : seq_table;
  v_huf : word; v_r0 : word; v_r1 : word; v_r2 : word; v_pde : word; v_dend : word; v_expd : word;
  v_pcs : word; v_dsz : word; v_bt : word; v_stg : word; v_le : word; v_fe : word;
  v_ws : list word;
  (* [comment removed for export] *)
  v_AI : AMallocIface; v_fflag : alayout -> Z -> Z -> Z; v_L : alayout; v_RNG : footprint; v_st : astate; v_LB : list ablock;
  v_m0 : amem;                      (* [comment removed for export] *)
  v_FRB : Z;                         (* [comment removed for export] *)
  v_FF : Z;                         (* [comment removed for export] *)
  v_SHF : Z;                        (* [comment removed for export] *)
  v_D8 : Z;                         (* [comment removed for export] *)
  v_j0 : list byte; v_j224 : list byte;     (* [comment removed for export] *)
  v_jfh : list byte; v_j144 : list byte;    (* [comment removed for export] *)
  v_jsh0 : list byte; v_jsh1 : list byte   (* [comment removed for export] *) }.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sqs_mem (P : ssq) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  seq_dctx m DCTX LLT MLT OFT huf r0 r1 r2 pde PFX PFX dend expd pcs dsz bt stg le fe ws /\ seq_lit2 ws LITP LBE LITB LOC /\
  bytes_at bsegs m SEQ (map (Z_to_bv 8) sq) /\ stk bsegs m B0 B1 /\
  rdbl bsegs m LITP (LBE + WILDCOPY_OVERLENGTH) /\
  (LOC = ZSTD_split -> rdbl bsegs m (DCTX + DCTX_litExtraBuffer) (DCTX + DCTX_litExtraBuffer + DCTX_litExtraBuffer_sz)) /\ mem_inv bsegs m.
Definition sqs_ranges (P : ssq) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  4096 <= DCTX /\ DCTX + DCTX_SIZEOF < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 0 <= nbSeq <= 98047 /\
  B0 <= DST /\ DST + CAP <= B1 /\ 0 <= CAP /\ B1 < 2^47 /\
  4096 <= LITP /\ LITP <= LBE /\ LBE + WILDCOPY_OVERLENGTH < 2^47 /\
  lo <= SPV - SEQ_SPLIT_STACK_A /\ 0 <= SPV < 2^47 /\ 4096 <= lo.
Definition sqs_side (P : ssq) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  DCTX mod 8 = 0 /\ all_bytes sq /\ (DST = 0 -> CAP = 0 /\ nbSeq = 0) /\ (DST <> 0 -> 4096 <= B0) /\ (nbSeq <> 0 -> B0 <= PFX <= DST) /\
  (LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst \/ LOC = ZSTD_split) /\
  (LOC = ZSTD_in_dst -> DST <= LITB <= DST + CAP /\ LITB <= LITP /\ LBE + WILDCOPY_OVERLENGTH <= B1) /\
  (LOC = ZSTD_not_in_dst -> apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) B0 (B1 - B0)) /\
  (LOC = ZSTD_split -> DST <= LITP /\ LBE + WILDCOPY_OVERLENGTH <= DST + CAP) /\
  SPV mod 16 = 0 /\ (nbSeq <> 0 -> LLT mod 8 = 0 /\ OFT mod 8 = 0 /\ MLT mod 8 = 0) /\ (nbSeq <> 0 -> 0 < CAP) /\
  (DST <> 0 -> B0 < B1) /\      (* [comment removed for export] *)
  LOC = ZSTD_split /\ 4096 <= B0.   (* [comment removed for export] *)
Definition sqs_sep (P : ssq) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  off_stack lo SPV DCTX DCTX_SIZEOF /\ off_stack lo SPV B0 (B1 - B0) /\ off_stack lo SPV SEQ (zlen sq) /\
  off_stack lo SPV LITP (LBE + WILDCOPY_OVERLENGTH - LITP) /\
  apart B0 (B1 - B0) DCTX DCTX_SIZEOF /\ apart B0 (B1 - B0) SEQ (zlen sq) /\
  apart SEQ (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  (LOC <> ZSTD_split -> apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep)).
Definition sqs_tables (P : ssq) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  seq_table_at m K_LL LLT tLL /\ seq_table_at m K_OF OFT tOF /\ seq_table_at m K_ML MLT tML /\
  4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47 /\
  off_stack lo SPV LLT (8 * (1 + 2^9)) /\ off_stack lo SPV OFT (8 * (1 + 2^8)) /\ off_stack lo SPV MLT (8 * (1 + 2^9)) /\
  apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ apart B0 (B1 - B0) MLT (8 * (1 + 2^9)) /\
  apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
  apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep).

(* [comment removed for export] *)
Definition sqs_asan (P : ssq) (m1 : amem) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  areg RNG m1 DCTX DCTX_SIZEOF /\ ahull RNG m1 DCTX DCTX_SIZEOF /\
  areg RNG m1 SEQ (zlen sq) /\
  (nbSeq <> 0 -> aro RNG m1 LLT (8 * (1 + 2 ^ st_log tLL)) /\ aro RNG m1 OFT (8 * (1 + 2 ^ st_log tOF)) /\ aro RNG m1 MLT (8 * (1 + 2 ^ st_log tML))) /\
  aro_client RNG m1 /\
  (B0 < B1 -> areg RNG m1 B0 (B1 - B0) /\ ahull RNG m1 B0 (B1 - B0)) /\
  areg RNG m1 LITP (LBE + WILDCOPY_OVERLENGTH - LITP) /\ ahull RNG m1 LITP (LBE + WILDCOPY_OVERLENGTH - LITP) /\
  azstk RNG m1 lo SPV /\ art m1.

(* [comment removed for export] *)
Definition sqs_astat (P : ssq) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  astk RNG lo SPV /\ tp = Z_to_bv 64 ATP /\ ATOP + 4096 <= lo /\ SPV + 16 < al_top L /\
  DCTX = 8 * D8 /\
  SPV - 400 <= FRB <= SPV - 384 /\ FRB mod 32 = 0 /\
  AIMG_HI <= FF /\ FF + 256 <= ATOP /\ FF mod 256 = 0 /\ SHF = shad FF /\ rng RNG FF 256 /\ rng RNG SHF 32 /\
  (* [comment removed for export] *)
  apart FF 256 DCTX DCTX_SIZEOF /\ (B0 < B1 -> apart FF 256 B0 (B1 - B0)) /\ (0 < zlen sq -> apart FF 256 SEQ (zlen sq)) /\   (* [comment removed for export] *)
  apart FF 256 LITP (LBE + WILDCOPY_OVERLENGTH - LITP) /\
  (nbSeq <> 0 -> apart FF 256 LLT (8 * (1 + 2^9)) /\ apart FF 256 OFT (8 * (1 + 2^8)) /\ apart FF 256 MLT (8 * (1 + 2^9))).

(* [comment removed for export] *)
Definition sqs_pro (P : ssq) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  AHEAP AI L RNG st (mkABlock (ABFake 2) FF 256 :: LB) m /\
  munch (fake_area L ++ [(SPV - SEQ_SPLIT_STACK_A, SPV)]) m0 m /\ wmono bsegs m0 m /\
  ffr_pres [] LB m0 m /\
  fake_flag_law AI fflag /\ fake_release_law AI fflag /\
  al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ /\
  (forall b, In b LB -> FF + 256 <= ab_addr b \/ ab_addr b + ab_size b <= FF) /\
  ainblk LB DCTX DCTX_SIZEOF /\ (B0 < B1 -> ainblk LB B0 (B1 - B0)) /\
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) /\     (* [comment removed for export] *)
  ablk FF (FF + 256).                                                       (* [comment removed for export] *)

Definition sqs_post (P : ssq) : machine_state -> Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  zd_seq_split_postA AI L RNG st LB SEQ_SPLIT_STACK_A ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 nbSeq pcs dsz bt stg le fe ws lo m0.

(* [comment removed for export] *)
Definition sqs_saved (P : ssq) : list cell := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition sqs_Wb (P : ssq) : list (Z * Z) := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
   (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4);
   (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)].

(* [comment removed for export] *)
Definition sqs_xinv (P : ssq) (m1 : amem) (fe' : word) : Prop := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  (exists r0' r1' r2', rw_cells bsegs m1 (DCTX + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) /\
  dctx_h3 bsegs m1 DCTX pcs dsz bt stg le fe' /\
  stk bsegs m1 B0 B1 /\ stk bsegs m1 lo FRB /\
  rw_cells bsegs m1 (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk bsegs m1 (FRB + 280) (SPV + -104) /\
  rw_cells bsegs m1 SHF [CB 4 jsh0; C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 14 jsh1] /\
  munch [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
         (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4);
         (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m m1 /\
  wmono bsegs m m1 /\ mem_inv bsegs m1.

(* [comment removed for export] *)
Definition sqs_fe (P : ssq) : word := if v_nbSeq P =? 0 then v_fe P else Z_to_bv 64 1.

End CANSEC1.

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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_rkit AZ_seq_l_v_lf AZ_seq_l_mkit AZ_seq_l_xat AZ_seq_l_lf_at AZ_seq_l_lm_at AZ_seq_l_s2_at AZ_seq_l_t2_at.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Local Ltac cells_split n H :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cl => rewrite <- (firstn_skipn n cl) in H; cbn [firstn skipn] in H end.
Local Ltac cells_split2 k H :=
  lazymatch type of H with rw_cells ?sg ?mm ?A (?pre ++ ?rest) => rewrite <- (firstn_skipn k rest) in H; cbn [firstn skipn] in H end.

Lemma lf_fsplit_ok : forall P OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  wnth (l_ws P) H5_litBufferEnd = Z_to_bv 64 LEND ->
  s2_exec P OEND LLO LEND LOCV K -> t2_brk P OEND LLO LEND LOCV K -> lf_fsplit P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLBE CONT1 CONT2.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold lf_fsplit. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c304 c328 c352 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP cidx raddr sn x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x28 x29 x30 INV LF HLOC HCV HRA HSN HSLO HRING.
  unfold s2_exec in CONT1. unfold t2_brk in CONT2. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in HK, CONT1, CONT2.
  pose proof ST as ST0.
  pose proof (sql_linv_frame _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 (Z_to_bv 64 3) (Z_to_bv 64 3) (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) c304 (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 (-65537)) c328 (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as TRANS. cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in TRANS.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & (H5C & H5L) & _). unfold h5_vcells in H5C. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in H5C, H5L. pose proof (sql_dctx_rng _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 (Z_to_bv 64 3) (Z_to_bv 64 3) (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) c304 (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 (-65537)) c328 (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (RDX0 & RDX). cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in RDX0, RDX.
  pose proof (sql_loc_shadow _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 (Z_to_bv 64 3) (Z_to_bv 64 3) (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) c304 (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 (-65537)) c328 (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (ZLBE & ZLOC & RLBE & RLOC & ED8 & RD8). cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in ZLBE, ZLOC, RLBE, RLOC, ED8, RD8.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 (Z_to_bv 64 3) (Z_to_bv 64 3) (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) c304 (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 (-65537)) c328 (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame] in FR. cbv delta [sql_ffr] in FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sql_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  sd_static_open ST. unfold held in RGB.
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  clear SQB USEQ RSQ RSQS UFL INV.
  cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in HLBE. rewrite HLBE in H5C.
  assert (RG : 4096 <= LP <= 2^47 - 32 /\ 4096 <= LEND <= 2^47 - 32 /\ 4096 <= OP < 2^47) by (clear - S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 L1 L2; lia). destruct RG as (RG3 & RG4 & RG5).
  assert (RGD : 4096 <= DCTX <= 2^47 - 95992) by (clear - S19 S20; lia). assert (DJD : (FRB + 568 <= DCTX \/ DCTX + 95992 <= FRB) /\ (FF + 256 <= DCTX \/ DCTX + 95992 <= FF)) by (unfold held in S27; unfold held in S54; clear - S27 S54 S18 S47; lia). destruct DJD as (DJD1 & DJD2).
  assert (HC8 : 0 <= cidx <= 7 /\ cidx < Z.min nbSeq 8). { rewrite HCV. split; [apply land7|]. change 7 with (Z.ones 3). rewrite Z.land_ones by (clear - HSN HSLO HK; lia). change (2^3) with 8. pose proof (Z.mod_pos_bound sn 8 ltac:(clear; lia)) as MB. destruct (Z.le_gt_cases 8 nbSeq) as [G8|L8]; [rewrite Z.min_r by (clear - G8; lia); clear - MB; lia | rewrite Z.min_l by (clear - L8; lia); rewrite Z.mod_small by (clear - HSN HSLO HK L8; lia); clear - HSN HSLO HK L8; lia]. } destruct HC8 as (HC7 & HCM).
  assert (CASES : cidx = 0 \/ cidx = 1 \/ cidx = 2 \/ cidx = 3 \/ cidx = 4 \/ cidx = 5 \/ cidx = 6 \/ cidx = 7) by (clear - HC7; lia).
  destruct CASES as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; rewrite C in HCV; subst cidx.
  - pose proof (HRING 0 ltac:(clear - HCM; lia)) as (RR1 & RR2 & RR3). assert (HCM2 : 0 <= 0 < Z.min nbSeq 8) by (clear - HCM; lia). assert (ERA : raddr = FRB + 344) by (clear - HRA; lia). clear HRA. subst raddr.
    cells_split 41%nat FR; apply (sql_ring_open_0 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold H5L; try hold HCV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZLOC; try hold RLOC; try hold ED8;
    kx_autoFLA (FR, FRF, H5C) [KAApp FRB 568; KAApp FF 256] [0x8d078; 0x8ce94] 40%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange DCTX 4096 (2^47 - 95992);
     KZDisj FRB 568 DCTX 95992;
     KZDisj FF 256 DCTX 95992;
     KZRange LOCV 2 2;
     KZRange LP 4096 (2^47 - 32);
     KZRange LEND 4096 (2^47 - 32);
     KZRange OP 4096 (2^47);
     KZRange (rl 0) 0 262143;
     KZRange (rm 0) 0 262143;
     KZRange (ro 0) 0 18446744073709551615;
     KZRange D8 512 17592186032416;
     KZWord (2147450880 + D8 + 3795) 1 0]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3795, 1)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in H5L; try unfold held in HCV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZLOC; try unfold held in RLOC; try unfold held in ED8; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d078) _ _ _ _) => (cells_split 41%nat FR; cells_split2 4%nat FR; apply sql_ring_shut_0 in FR; cbn [app] in FR; eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR3; lia | clear - RR1; lia | clear - RR2; lia | clear; lia | clear - KXBR RG3 RG4 RR1; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | exact HSN | exact HSLO | exact HRING | exact HLOC ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ce94) _ _ _ _) => (cells_split 41%nat FR; cells_split2 4%nat FR; apply sql_ring_shut_0 in FR; cbn [app] in FR; eapply CONT2 with (cidx := 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR1; lia | clear; lia | kx_bv_ranges; kx_lia_pruned | exact HLOC | exact HCV | clear; lia | reflexivity | exact HSN | exact HSLO | exact HRING ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - pose proof (HRING 1 ltac:(clear - HCM; lia)) as (RR1 & RR2 & RR3). assert (HCM2 : 0 <= 1 < Z.min nbSeq 8) by (clear - HCM; lia). assert (ERA : raddr = FRB + 368) by (clear - HRA; lia). clear HRA. subst raddr.
    cells_split 41%nat FR; apply (sql_ring_open_1 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold H5L; try hold HCV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZLOC; try hold RLOC; try hold ED8;
    kx_autoFLA (FR, FRF, H5C) [KAApp FRB 568; KAApp FF 256] [0x8d078; 0x8ce94] 40%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange DCTX 4096 (2^47 - 95992);
     KZDisj FRB 568 DCTX 95992;
     KZDisj FF 256 DCTX 95992;
     KZRange LOCV 2 2;
     KZRange LP 4096 (2^47 - 32);
     KZRange LEND 4096 (2^47 - 32);
     KZRange OP 4096 (2^47);
     KZRange (rl 1) 0 262143;
     KZRange (rm 1) 0 262143;
     KZRange (ro 1) 0 18446744073709551615;
     KZRange D8 512 17592186032416;
     KZWord (2147450880 + D8 + 3795) 1 0]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3795, 1)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in H5L; try unfold held in HCV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZLOC; try unfold held in RLOC; try unfold held in ED8; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d078) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_1 in FR; cbn [app] in FR; eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR3; lia | clear - RR1; lia | clear - RR2; lia | clear; lia | clear - KXBR RG3 RG4 RR1; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | exact HSN | exact HSLO | exact HRING | exact HLOC ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ce94) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_1 in FR; cbn [app] in FR; eapply CONT2 with (cidx := 1); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR1; lia | clear; lia | kx_bv_ranges; kx_lia_pruned | exact HLOC | exact HCV | clear; lia | reflexivity | exact HSN | exact HSLO | exact HRING ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - pose proof (HRING 2 ltac:(clear - HCM; lia)) as (RR1 & RR2 & RR3). assert (HCM2 : 0 <= 2 < Z.min nbSeq 8) by (clear - HCM; lia). assert (ERA : raddr = FRB + 392) by (clear - HRA; lia). clear HRA. subst raddr.
    cells_split 41%nat FR; apply (sql_ring_open_2 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold H5L; try hold HCV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZLOC; try hold RLOC; try hold ED8;
    kx_autoFLA (FR, FRF, H5C) [KAApp FRB 568; KAApp FF 256] [0x8d078; 0x8ce94] 40%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange DCTX 4096 (2^47 - 95992);
     KZDisj FRB 568 DCTX 95992;
     KZDisj FF 256 DCTX 95992;
     KZRange LOCV 2 2;
     KZRange LP 4096 (2^47 - 32);
     KZRange LEND 4096 (2^47 - 32);
     KZRange OP 4096 (2^47);
     KZRange (rl 2) 0 262143;
     KZRange (rm 2) 0 262143;
     KZRange (ro 2) 0 18446744073709551615;
     KZRange D8 512 17592186032416;
     KZWord (2147450880 + D8 + 3795) 1 0]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3795, 1)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in H5L; try unfold held in HCV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZLOC; try unfold held in RLOC; try unfold held in ED8; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d078) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_2 in FR; cbn [app] in FR; eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR3; lia | clear - RR1; lia | clear - RR2; lia | clear; lia | clear - KXBR RG3 RG4 RR1; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | exact HSN | exact HSLO | exact HRING | exact HLOC ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ce94) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_2 in FR; cbn [app] in FR; eapply CONT2 with (cidx := 2); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR1; lia | clear; lia | kx_bv_ranges; kx_lia_pruned | exact HLOC | exact HCV | clear; lia | reflexivity | exact HSN | exact HSLO | exact HRING ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - pose proof (HRING 3 ltac:(clear - HCM; lia)) as (RR1 & RR2 & RR3). assert (HCM2 : 0 <= 3 < Z.min nbSeq 8) by (clear - HCM; lia). assert (ERA : raddr = FRB + 416) by (clear - HRA; lia). clear HRA. subst raddr.
    cells_split 41%nat FR; apply (sql_ring_open_3 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold H5L; try hold HCV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZLOC; try hold RLOC; try hold ED8;
    kx_autoFLA (FR, FRF, H5C) [KAApp FRB 568; KAApp FF 256] [0x8d078; 0x8ce94] 40%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange DCTX 4096 (2^47 - 95992);
     KZDisj FRB 568 DCTX 95992;
     KZDisj FF 256 DCTX 95992;
     KZRange LOCV 2 2;
     KZRange LP 4096 (2^47 - 32);
     KZRange LEND 4096 (2^47 - 32);
     KZRange OP 4096 (2^47);
     KZRange (rl 3) 0 262143;
     KZRange (rm 3) 0 262143;
     KZRange (ro 3) 0 18446744073709551615;
     KZRange D8 512 17592186032416;
     KZWord (2147450880 + D8 + 3795) 1 0]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3795, 1)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in H5L; try unfold held in HCV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZLOC; try unfold held in RLOC; try unfold held in ED8; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d078) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_3 in FR; cbn [app] in FR; eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR3; lia | clear - RR1; lia | clear - RR2; lia | clear; lia | clear - KXBR RG3 RG4 RR1; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | exact HSN | exact HSLO | exact HRING | exact HLOC ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ce94) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_3 in FR; cbn [app] in FR; eapply CONT2 with (cidx := 3); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR1; lia | clear; lia | kx_bv_ranges; kx_lia_pruned | exact HLOC | exact HCV | clear; lia | reflexivity | exact HSN | exact HSLO | exact HRING ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - pose proof (HRING 4 ltac:(clear - HCM; lia)) as (RR1 & RR2 & RR3). assert (HCM2 : 0 <= 4 < Z.min nbSeq 8) by (clear - HCM; lia). assert (ERA : raddr = FRB + 440) by (clear - HRA; lia). clear HRA. subst raddr.
    cells_split 41%nat FR; apply (sql_ring_open_4 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold H5L; try hold HCV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZLOC; try hold RLOC; try hold ED8;
    kx_autoFLA (FR, FRF, H5C) [KAApp FRB 568; KAApp FF 256] [0x8d078; 0x8ce94] 40%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange DCTX 4096 (2^47 - 95992);
     KZDisj FRB 568 DCTX 95992;
     KZDisj FF 256 DCTX 95992;
     KZRange LOCV 2 2;
     KZRange LP 4096 (2^47 - 32);
     KZRange LEND 4096 (2^47 - 32);
     KZRange OP 4096 (2^47);
     KZRange (rl 4) 0 262143;
     KZRange (rm 4) 0 262143;
     KZRange (ro 4) 0 18446744073709551615;
     KZRange D8 512 17592186032416;
     KZWord (2147450880 + D8 + 3795) 1 0]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3795, 1)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in H5L; try unfold held in HCV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZLOC; try unfold held in RLOC; try unfold held in ED8; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d078) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_4 in FR; cbn [app] in FR; eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR3; lia | clear - RR1; lia | clear - RR2; lia | clear; lia | clear - KXBR RG3 RG4 RR1; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | exact HSN | exact HSLO | exact HRING | exact HLOC ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ce94) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_4 in FR; cbn [app] in FR; eapply CONT2 with (cidx := 4); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR1; lia | clear; lia | kx_bv_ranges; kx_lia_pruned | exact HLOC | exact HCV | clear; lia | reflexivity | exact HSN | exact HSLO | exact HRING ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - pose proof (HRING 5 ltac:(clear - HCM; lia)) as (RR1 & RR2 & RR3). assert (HCM2 : 0 <= 5 < Z.min nbSeq 8) by (clear - HCM; lia). assert (ERA : raddr = FRB + 464) by (clear - HRA; lia). clear HRA. subst raddr.
    cells_split 41%nat FR; apply (sql_ring_open_5 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold H5L; try hold HCV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZLOC; try hold RLOC; try hold ED8;
    kx_autoFLA (FR, FRF, H5C) [KAApp FRB 568; KAApp FF 256] [0x8d078; 0x8ce94] 40%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange DCTX 4096 (2^47 - 95992);
     KZDisj FRB 568 DCTX 95992;
     KZDisj FF 256 DCTX 95992;
     KZRange LOCV 2 2;
     KZRange LP 4096 (2^47 - 32);
     KZRange LEND 4096 (2^47 - 32);
     KZRange OP 4096 (2^47);
     KZRange (rl 5) 0 262143;
     KZRange (rm 5) 0 262143;
     KZRange (ro 5) 0 18446744073709551615;
     KZRange D8 512 17592186032416;
     KZWord (2147450880 + D8 + 3795) 1 0]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3795, 1)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in H5L; try unfold held in HCV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZLOC; try unfold held in RLOC; try unfold held in ED8; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d078) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_5 in FR; cbn [app] in FR; eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR3; lia | clear - RR1; lia | clear - RR2; lia | clear; lia | clear - KXBR RG3 RG4 RR1; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | exact HSN | exact HSLO | exact HRING | exact HLOC ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ce94) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_5 in FR; cbn [app] in FR; eapply CONT2 with (cidx := 5); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR1; lia | clear; lia | kx_bv_ranges; kx_lia_pruned | exact HLOC | exact HCV | clear; lia | reflexivity | exact HSN | exact HSLO | exact HRING ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - pose proof (HRING 6 ltac:(clear - HCM; lia)) as (RR1 & RR2 & RR3). assert (HCM2 : 0 <= 6 < Z.min nbSeq 8) by (clear - HCM; lia). assert (ERA : raddr = FRB + 488) by (clear - HRA; lia). clear HRA. subst raddr.
    cells_split 41%nat FR; apply (sql_ring_open_6 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold H5L; try hold HCV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZLOC; try hold RLOC; try hold ED8;
    kx_autoFLA (FR, FRF, H5C) [KAApp FRB 568; KAApp FF 256] [0x8d078; 0x8ce94] 40%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange DCTX 4096 (2^47 - 95992);
     KZDisj FRB 568 DCTX 95992;
     KZDisj FF 256 DCTX 95992;
     KZRange LOCV 2 2;
     KZRange LP 4096 (2^47 - 32);
     KZRange LEND 4096 (2^47 - 32);
     KZRange OP 4096 (2^47);
     KZRange (rl 6) 0 262143;
     KZRange (rm 6) 0 262143;
     KZRange (ro 6) 0 18446744073709551615;
     KZRange D8 512 17592186032416;
     KZWord (2147450880 + D8 + 3795) 1 0]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3795, 1)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in H5L; try unfold held in HCV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZLOC; try unfold held in RLOC; try unfold held in ED8; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d078) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_6 in FR; cbn [app] in FR; eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR3; lia | clear - RR1; lia | clear - RR2; lia | clear; lia | clear - KXBR RG3 RG4 RR1; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | exact HSN | exact HSLO | exact HRING | exact HLOC ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ce94) _ _ _ _) => (cells_split 41%nat FR; cells_split2 5%nat FR; apply sql_ring_shut_6 in FR; cbn [app] in FR; eapply CONT2 with (cidx := 6); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR1; lia | clear; lia | kx_bv_ranges; kx_lia_pruned | exact HLOC | exact HCV | clear; lia | reflexivity | exact HSN | exact HSLO | exact HRING ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - pose proof (HRING 7 ltac:(clear - HCM; lia)) as (RR1 & RR2 & RR3). assert (HCM2 : 0 <= 7 < Z.min nbSeq 8) by (clear - HCM; lia). assert (ERA : raddr = FRB + 512) by (clear - HRA; lia). clear HRA. subst raddr.
    cells_split 41%nat FR; apply (sql_ring_open_7 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR; cbn [app] in FR.
    (try hold CONT1; try hold CONT2; try hold HK; try hold ST0; try hold TRANS; try hold HRING; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold H5L; try hold HCV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZLOC; try hold RLOC; try hold ED8;
    kx_autoFLA (FR, FRF, H5C) [KAApp FRB 568; KAApp FF 256] [0x8d078; 0x8ce94] 40%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZRange DCTX 4096 (2^47 - 95992);
     KZDisj FRB 568 DCTX 95992;
     KZDisj FF 256 DCTX 95992;
     KZRange LOCV 2 2;
     KZRange LP 4096 (2^47 - 32);
     KZRange LEND 4096 (2^47 - 32);
     KZRange OP 4096 (2^47);
     KZRange (rl 7) 0 262143;
     KZRange (rm 7) 0 262143;
     KZRange (ro 7) 0 18446744073709551615;
     KZRange D8 512 17592186032416;
     KZWord (2147450880 + D8 + 3795) 1 0]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
    [(FRB, 568); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3795, 1)];
    try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in CONT2; try unfold held in HK; try unfold held in ST0; try unfold held in TRANS; try unfold held in HRING; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in H5L; try unfold held in HCV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZLOC; try unfold held in RLOC; try unfold held in ED8; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8d078) _ _ _ _) => (cells_split 41%nat FR; cells_split2 4%nat FR; apply sql_ring_shut_7 in FR; cbn [app] in FR; eapply CONT1; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR3; lia | clear - RR1; lia | clear - RR2; lia | clear; lia | clear - KXBR RG3 RG4 RR1; first [lia | (rewrite ?Z.mod_small in * by lia; lia)] | exact HSN | exact HSLO | exact HRING | exact HLOC ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8ce94) _ _ _ _) => (cells_split 41%nat FR; cells_split2 4%nat FR; apply sql_ring_shut_7 in FR; cbn [app] in FR; eapply CONT2 with (cidx := 7); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | exact LF0 | clear - RR1; lia | clear; lia | kx_bv_ranges; kx_lia_pruned | exact HLOC | exact HCV | clear; lia | reflexivity | exact HSN | exact HSLO | exact HRING ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End CANSEC1.

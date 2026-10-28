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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_v_x2 AZ_seq_l_hkit AZ_seq_l_lkit2 AZ_seq_l_ckit AZ_seq_l_xat AZ_seq_l_s2_at.
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

Lemma s2_exec6b : forall P OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  s2_close8 P OEND LLO LEND LOCV K -> s2_close_sel (fun o => 4 <= o <= 6) P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold s2_close_sel. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c120 c128 c160 c232 c320 c352 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ole mlv sl ofs mtc dpx sn x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x22 x23 x27 x28 x29 x30 x31 INV LF MF HO HOF HM HXclose1 HSN HSLO HRING HLOC HSEL.
  unfold s2_close8 in CONT1. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in HK, CONT1.
  pose proof ST as ST0.
  pose proof (sql_linv_buf _ _ _ _ _ m1 c8 c16 c24 c32 c88 (Z_to_bv 64 sl) c120 c128 c160 (Z_to_bv 64 3) c232 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 LEND) (Z_to_bv 64 (DCTX + 95908)) c320 (Z_to_bv 64 ofs) (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as BUFS. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in BUFS.
  pose proof (sql_copy_facts _ _ _ _ _ m1 c8 c16 c24 c32 c88 (Z_to_bv 64 sl) c120 c128 c160 (Z_to_bv 64 3) c232 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 LEND) (Z_to_bv 64 (DCTX + 95908)) c320 (Z_to_bv 64 ofs) (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (BUF & LIT & STK & CFA). cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in BUF, LIT, STK, CFA.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 (Z_to_bv 64 sl) c120 c128 c160 (Z_to_bv 64 3) c232 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 LEND) (Z_to_bv 64 (DCTX + 95908)) c320 (Z_to_bv 64 ofs) (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (DCTX + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  apply sql_fr_vx2 in FR. cbv delta [sql_ffr] in FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sql_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof MF as MF0. destruct MF as (M1 & M2 & M3 & M4). cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in M1.
  apply (sql_buf_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros BUFB UBUF RBUF RBUFS GRAN U32 R32 RS32 U64 R64 RS64 TBG.
  sd_static_open ST. unfold held in RGB.
  assert (LE32 : LEND + 32 <= OEND) by (unfold held in S42; clear - S42 HLOC; lia).
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  cbv beta in HSEL. clear MUL.     (* [comment removed for export] *)
  assert (RG : 4096 <= ole /\ ole + 9 <= 2^47 /\ 4096 <= mtc /\ mtc <= ole /\ B0 <= mtc /\ ole + 8 <= B1 /\ DST <= ole /\ ole + 8 <= OEND /\ B1 < 2^47 /\ mtc = ole - ofs)
    by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HO HOF HM; lia).
  assert (RGM : ole + 16 - ole mod 8 <= B1) by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HO HOF HM; Z.div_mod_to_equations; lia).
  assert (MUL6 : munch [(ole, ole + 8); (FRB - 2224, FRB)] m1 m1) by apply munch_refl.
  assert (KDO : ole + 8 <= FRB \/ FRB + 568 <= ole) by (unfold held in S24; clear - S24 RG RGA5 RGA6 HM HO; lia).
  assert (KDF : ole + 8 <= FF \/ FF + 256 <= ole) by (unfold held in S55; clear - S55 RG HM HO; lia).
  assert (KAO : ole + 8 <= 2147450880 \/ 17594333495296 <= ole) by (unfold held in S69; clear - S69 RG; lia).     (* [comment removed for export] *)
  assert (ZSH2 : rng RNG (KXSHLO + 0x22240 / 8) (shspanZ 0x22240 32)) by exact (shz_lit RNG 0x22240 32 RS32).
  assert (ZSH3 : rng RNG (KXSHLO + 0x22280 / 8) (shspanZ 0x22280 32)) by exact (shz_lit RNG 0x22280 32 RS64).
  assert (CASES : ofs = 4 \/ ofs = 5 \/ ofs = 6) by (clear - HO HSEL; lia).
  destruct CASES as [C|[C|C]].
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 4) by (clear - HM; lia). subst mtc.
    destruct (TBG 17490 ltac:(clear; lia)) as (ZT64 & RT64). change (rng RNG 2147468370 1) in RT64. destruct (TBG 17482 ltac:(clear; lia)) as (ZT32 & RT32). change (rng RNG 2147468362 1) in RT32.
    assert (ZSH1 : rng RNG (KXSHLO + (ole - 4) / 8) (shspanZ (ole - 4) 12)) by (apply (shz_sub RNG B0 (B1 - B0) (ole - 4) 12 RBUFS); clear - RG; lia).
    assert (UZ1 : unpZ m1 (ole - 4) ((ole - 4) + 12)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (ole - 4) ((ole - 4) + 12) UBUF); unfold KXKEND; clear - RG; lia).
    assert (WN1 : rng RNG (ole - 4) 12) by (eapply rng_sub; [exact RBUF | clear - RG; lia | clear - RG; lia]).
    (try hold CONT1; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HO; try hold HSEL; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZT64; try hold ZT32; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp (ole - 4) 12; KAApp ole 8; KAUnp 0x22240 32; KAUnp 0x22280 32] [0x8de64; 0x8e3dc; 0x8e3ec; 0x8e3f8; 0x8e404; 0x8e410; 0x8e41c; 0x8e428; 0x8e434; 0x8e440; 0x8e44c; 0x8e45c; 0x8e468; 0x8e474; 0x8e480; 0x8e48c; 0x8e498; 0x8e4a4; 0x8e4b0] 400%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange ole 4096 (2^47 - 9);
     KZRange (ole - 4) 4096 (2^47 - 13);
     KZWr ole 8;
     KZDisj ole 8 FRB 568;
     KZDisj ole 8 FF 256;
     KZImg 0x22240 0x222cb;
     KZWord (2147450880 + 17490) 1 0;
     KZWord (2147450880 + 17482) 1 0;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568]
    [(ole - 4, 12); (FRB, 568); (FF, 256)]
    [(ole - 4, 12); (0x22240, 32); (0x22280, 32); (2147468370, 1); (2147468362, 1); (FRB, 568); (FF, 256)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HO; try unfold held in HSEL; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZT64; try unfold held in ZT32; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8de64) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [eapply BUFS; [exact MUL6 | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1; lia | clear - M1 M2 M3; lia] | exact LF0 | exact MF0 | cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 5) by (clear - HM; lia). subst mtc.
    destruct (TBG 17490 ltac:(clear; lia)) as (ZT64 & RT64). change (rng RNG 2147468370 1) in RT64. destruct (TBG 17482 ltac:(clear; lia)) as (ZT32 & RT32). change (rng RNG 2147468362 1) in RT32.
    assert (ZSH1 : rng RNG (KXSHLO + (ole - 5) / 8) (shspanZ (ole - 5) 13)) by (apply (shz_sub RNG B0 (B1 - B0) (ole - 5) 13 RBUFS); clear - RG; lia).
    assert (UZ1 : unpZ m1 (ole - 5) ((ole - 5) + 13)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (ole - 5) ((ole - 5) + 13) UBUF); unfold KXKEND; clear - RG; lia).
    assert (WN1 : rng RNG (ole - 5) 13) by (eapply rng_sub; [exact RBUF | clear - RG; lia | clear - RG; lia]).
    (try hold CONT1; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HO; try hold HSEL; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZT64; try hold ZT32; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp (ole - 5) 13; KAApp ole 8; KAUnp 0x22240 32; KAUnp 0x22280 32] [0x8de64; 0x8e3dc; 0x8e3ec; 0x8e3f8; 0x8e404; 0x8e410; 0x8e41c; 0x8e428; 0x8e434; 0x8e440; 0x8e44c; 0x8e45c; 0x8e468; 0x8e474; 0x8e480; 0x8e48c; 0x8e498; 0x8e4a4; 0x8e4b0] 400%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange ole 4096 (2^47 - 9);
     KZRange (ole - 5) 4096 (2^47 - 14);
     KZWr ole 8;
     KZDisj ole 8 FRB 568;
     KZDisj ole 8 FF 256;
     KZImg 0x22240 0x222cb;
     KZWord (2147450880 + 17490) 1 0;
     KZWord (2147450880 + 17482) 1 0;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568]
    [(ole - 5, 13); (FRB, 568); (FF, 256)]
    [(ole - 5, 13); (0x22240, 32); (0x22280, 32); (2147468370, 1); (2147468362, 1); (FRB, 568); (FF, 256)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HO; try unfold held in HSEL; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZT64; try unfold held in ZT32; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8de64) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [eapply BUFS; [exact MUL6 | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1; lia | clear - M1 M2 M3; lia] | exact LF0 | exact MF0 | cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 6) by (clear - HM; lia). subst mtc.
    destruct (TBG 17491 ltac:(clear; lia)) as (ZT64 & RT64). change (rng RNG 2147468371 1) in RT64. destruct (TBG 17483 ltac:(clear; lia)) as (ZT32 & RT32). change (rng RNG 2147468363 1) in RT32.
    assert (ZSH1 : rng RNG (KXSHLO + (ole - 6) / 8) (shspanZ (ole - 6) 14)) by (apply (shz_sub RNG B0 (B1 - B0) (ole - 6) 14 RBUFS); clear - RG; lia).
    assert (UZ1 : unpZ m1 (ole - 6) ((ole - 6) + 14)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (ole - 6) ((ole - 6) + 14) UBUF); unfold KXKEND; clear - RG; lia).
    assert (WN1 : rng RNG (ole - 6) 14) by (eapply rng_sub; [exact RBUF | clear - RG; lia | clear - RG; lia]).
    (try hold CONT1; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HO; try hold HSEL; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML; try hold ZT64; try hold ZT32; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO;
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp (ole - 6) 14; KAApp ole 8; KAUnp 0x22240 32; KAUnp 0x22280 32] [0x8de64; 0x8e3dc; 0x8e3ec; 0x8e3f8; 0x8e404; 0x8e410; 0x8e41c; 0x8e428; 0x8e434; 0x8e440; 0x8e44c; 0x8e45c; 0x8e468; 0x8e474; 0x8e480; 0x8e48c; 0x8e498; 0x8e4a4; 0x8e4b0] 400%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange ole 4096 (2^47 - 9);
     KZRange (ole - 6) 4096 (2^47 - 15);
     KZWr ole 8;
     KZDisj ole 8 FRB 568;
     KZDisj ole 8 FF 256;
     KZImg 0x22240 0x222cb;
     KZWord (2147450880 + 17491) 1 0;
     KZWord (2147450880 + 17483) 1 0;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568]
    [(ole - 6, 14); (FRB, 568); (FF, 256)]
    [(ole - 6, 14); (0x22240, 32); (0x22280, 32); (2147468371, 1); (2147468363, 1); (FRB, 568); (FF, 256)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sql_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HO; try unfold held in HSEL; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZT64; try unfold held in ZT32; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8de64) _ _ _ _) => (eapply CONT1 with (ole := ole) (mlv := mlv); [eapply BUFS; [exact MUL6 | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1; lia | clear - M1 M2 M3; lia] | exact LF0 | exact MF0 | cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; lia | lia | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
Qed.

End CANSEC1.

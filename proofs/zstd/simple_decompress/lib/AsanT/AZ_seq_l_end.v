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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_v_lz AZ_seq_l_ekit AZ_seq_l_lkit2 AZ_seq_l_zkit AZ_seq_l_fin AZ_seq_l_last2 AZ_seq_l_lastx AZ_seq_l_xat AZ_seq_l_lf_at.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac le_blob_seg H a b :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn a cs) in
    let mid := eval cbn [firstn skipn Nat.sub] in (firstn (Nat.sub b a) (skipn a cs)) in
    let post := eval cbn [skipn] in (skipn b cs) in
    change (rw_cells sg mm A (pre ++ mid ++ post)) in H;
    apply (rw_cells_merge sg mm A pre mid post) in H;
    cbn [app cells_size csize Nat.add length] in H
  end.

Section CANSEC1. Context {rc : runConstT}.

Lemma lf_end_ok : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> sql_at_lastx P -> lf_end P OEND LLO LEND LOCV 1.
Proof.
  intros P OEND LLO LEND LOCV ST LASTK.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold lf_end. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c248 c264 c304 c312 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP x1 x5 x6 x7 x11 x12 x13 x15 x16 x17 x18 x20 x24 x27 x28 x29 x30 INV LF.
  unfold sql_at_lastx, sql_fe in LASTK. cbn [sql_saved l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in LASTK. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in LASTK.
  pose proof ST as ST0.
  pose proof (sql_rep_shadow _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 (Z_to_bv 64 3) c248 c264 c304 c312 (Z_to_bv 64 (-65537)) c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (RZ0 & RZ1 & RR0 & RR1 & ED8 & RD8). cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in RZ0, RZ1, RR0, RR1, ED8, RD8.
  pose proof (sql_loc_shadow _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 (Z_to_bv 64 3) c248 c264 c304 c312 (Z_to_bv 64 (-65537)) c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (_ & ZLOC & _ & RLOC & _ & _). cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in ZLOC, RLOC.
  pose proof (sql_asan_now _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 (Z_to_bv 64 3) c248 c264 c304 c312 (Z_to_bv 64 (-65537)) c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as AS1. cbn [sql_asan l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in AS1. destruct AS1 as (ARD1 & _ & _ & _ & _ & _ & ARL & _). unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in ARD1, ARL.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 (Z_to_bv 64 3) c248 c264 c304 c312 (Z_to_bv 64 (-65537)) c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sql_frame sql_ffr] in FR, FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sql_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & LIT & XLIT & (H5C & H5L) & XI). cbn [sql_xinv l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in XI, LIT, XLIT, H5C, H5L. unfold sql_fe in XI. unfold h5_vcells in H5C.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS LF.
  sd_static_open ST. unfold held in RGB.
  (* [comment removed for export] *)
  pose proof atop_range as ATR.
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { destruct (ARD1 ltac:(clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. exact BL. }
  assert (BLL : (6443008 <= LLO /\ LEND + 32 <= 2147446784) \/ (17594333495296 <= LLO /\ LEND + 32 <= ATOP)).
  { unfold held in S67. destruct S67 as [(EL1 & EL2)|(EL1 & EL2)].
    - destruct (ARL ltac:(unfold held in S70; clear - S70; lia)) as (BL & _). pose proof (ablk_lits _ _ BL) as BL2. clear - BL2 EL1 EL2. lia.
    - clear - BDL EL1 EL2. lia. }
  assert (RG : 512 <= D8 /\ D8 + 11999 < 2^44 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= OP < 2^47 /\ 4096 <= LEND < 2^47 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495296)
    by (unfold held in S53; clear - ED8 S19 S20 S1 S2 S3 S4 S5 S6 S7 S9 S11 L1 L2 RGC1 RGA2 S53; lia).
  destruct RG as (RG1 & RG1b & RG2 & RG2b & RG3 & RG4 & RSH1 & RSH2).
  (* [comment removed for export] *)
  assert (KD1 : DCTX + 26684 + 12 <= FRB \/ FRB + 568 <= DCTX + 26684) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (KD2 : DCTX + 26684 + 12 <= FF \/ FF + 256 <= DCTX + 26684) by (unfold held in S54; clear - S54; lia).
  assert (KD3 : DCTX + 26684 + 12 <= SHF \/ SHF + 32 <= DCTX + 26684) by (clear - BDL RGC1 RGA1 RGA2 RGA8 RGB ATR; lia).
  assert (KD4 : DCTX + 26684 + 12 <= 2147450880 + D8 + 3335 \/ 2147450880 + D8 + 3335 + 1 <= DCTX + 26684) by (clear - BDL ED8 ATR; lia).
  assert (KD4b : DCTX + 26684 + 12 <= 2147450880 + D8 + 3336 \/ 2147450880 + D8 + 3336 + 1 <= DCTX + 26684) by (clear - BDL ED8 ATR; lia).
  assert (KD5 : SHF + 32 <= 2147450880 + D8 + 3335 \/ 2147450880 + D8 + 3335 + 1 <= SHF) by (unfold held in S54; clear - S54 RGC1 RGC2 ED8 RG1; Z.div_mod_to_equations; lia).
  assert (KD5b : SHF + 32 <= 2147450880 + D8 + 3336 \/ 2147450880 + D8 + 3336 + 1 <= SHF) by (unfold held in S54; clear - S54 RGC1 RGC2 ED8 RG1; Z.div_mod_to_equations; lia).
  assert (KD6 : SHF + 32 <= FF \/ FF + 256 <= SHF) by (clear - RGB RGC1 RGA2; lia).
  assert (KD7 : SHF + 32 <= FRB \/ FRB + 568 <= SHF) by (clear - RGC1 RGA2 RGA1 RGA7 RGA8; lia).
  assert (KD8 : DCTX + 26684 + 12 <= 2147450880 + D8 + 3796 \/ 2147450880 + D8 + 3796 + 1 <= DCTX + 26684) by (clear - BDL ED8 ATR; lia).
  assert (KD9 : SHF + 32 <= 2147450880 + D8 + 3796 \/ 2147450880 + D8 + 3796 + 1 <= SHF) by (unfold held in S54; clear - S54 RGC1 RGC2 ED8 RG1; Z.div_mod_to_equations; lia).
  assert (MUX : munch [(SHF, SHF + 32); (DCTX + 26684, DCTX + 26684 + 12)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sql_blob_all SHS.     (* [comment removed for export] *)
  destruct (ARD1 ltac:(clear; lia)) as (_ & _ & RDD & _). clear ARD1.      (* [comment removed for export] *)
  try hold LASTK; try hold ST0; try hold LF0; try hold L1; try hold L2; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold HH3; try hold H5C; try hold H5L; try hold BUF; try hold STK; try hold SAV; try hold GAP; try hold MU; try hold WM; try hold LIT; try hold XLIT; try hold BLL; try hold BDL; try hold L16F; try hold LJF; try hold ED8; try hold ARL; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold S71; try hold OKLL; try hold OKOF; try hold OKML.
  (* [comment removed for export] *)
  revert RG1 RG1b RG2 RG2b RG3 RG4 RSH1 RSH2 S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB; rhold_arith; intros RG1 RG1b RG2 RG2b RG3 RG4 RSH1 RSH2 S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB.
  kx_autoFLA (FR, FRF, REP, SHS) [] [0x89e20] 60%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 672);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZAlign FF 8;
     KZRange SHF 2147450880 (17594333495296 - 32);
     KZRange D8 512 (2^44 - 11999);
     KZRange DCTX 4096 (2^47 - 95992);
     KZRange OP 4096 (2^47);
     KZRange LEND 4096 (2^47);
     KZWord (2147450880 + D8 + 3335) 1 0;
     KZWord (2147450880 + D8 + 3336) 1 0;
     KZWord (2147450880 + D8 + 3796) 1 0;
     KZWr FRB 568;
     KZWr FF 256;
     KZDisj FF 256 FRB 568;
     KZWr SHF 32;
     KZWr (DCTX + 26684) 12;
     KZDisj SHF 32 FRB 568;
     KZDisj SHF 32 FF 256;
     KZDisj (DCTX + 26684) 12 FRB 568;
     KZDisj (DCTX + 26684) 12 FF 256;
     KZDisj (DCTX + 26684) 12 SHF 32;
     KZDisj (DCTX + 26684) 12 (2147450880 + D8 + 3335) 1;
     KZDisj (DCTX + 26684) 12 (2147450880 + D8 + 3336) 1;
     KZDisj (DCTX + 26684) 12 (2147450880 + D8 + 3796) 1;
     KZDisj SHF 32 (2147450880 + D8 + 3335) 1;
     KZDisj SHF 32 (2147450880 + D8 + 3336) 1;
     KZDisj SHF 32 (2147450880 + D8 + 3796) 1]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32); (DCTX + 26684, 12); (2147450880 + D8 + 3335, 1); (2147450880 + D8 + 3336, 1); (2147450880 + D8 + 3796, 1)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: runhold_off.
  all: (try unfold held in LASTK; try unfold held in ST0; try unfold held in LF0; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in HH3; try unfold held in H5C; try unfold held in H5L; try unfold held in BUF; try unfold held in STK; try unfold held in SAV; try unfold held in GAP; try unfold held in MU; try unfold held in WM; try unfold held in LIT; try unfold held in XLIT; try unfold held in BLL; try unfold held in BDL; try unfold held in L16F; try unfold held in LJF; try unfold held in ED8; try unfold held in ARL; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x89e20) _ _ ?mx _) =>
         unfold held in BDL; unfold held in BLL;
         (* [comment removed for export] *)
         assert (MU2 : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
           by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
         assert (WM2 : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WMX]);
         pose proof (sql_asan_transport (mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) _ _ _ _ mx ST0 MU2 WM2) as AS2;
         (* [comment removed for export] *)
         assert (BUF' : stk bsegs mx B0 B1) by (eapply stk_transport_disjoint; [exact BUF | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S69; unfold held in S32; unfold held in S68; clear - S69 S32 S52 RSH2 S68; lia]);
         assert (STK' : stk bsegs mx lo FRB) by (eapply stk_transport_disjoint; [exact STK | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S27; unfold held in S53; clear - S27 S53 S47 S18; lia]);
         assert (GAP' : stk bsegs mx (FRB + 568) (SPV + -104)) by (eapply stk_transport_disjoint; [exact GAP | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S27; unfold held in S53; clear - S27 S53 S47 S18; lia]);
         assert (SAV' : rw_cells bsegs mx (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
           by (eapply rw_cells_transport; [exact SAV | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; simpl_sizes; unfold held in S27; unfold held in S53; clear - S27 S53 S47 S18; lia]);
         assert (HH3' : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
           by (eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - BDL RGC1 RGA1 RGA2 RGA8 RGB ATR; lia|]; split; [clear; lia| exact I]]);
         assert (H5V' : rw_cells bsegs mx (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (Z_to_bv 64 LOCV)])
           by (eapply rw_cells_transport; [exact H5C | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - BDL RGC1 RGA1 RGA2 RGA8 RGB ATR; lia|]; split; [clear; lia| exact I]]);
         assert (LIT' : rdbl bsegs mx LP (LEND + 32))
           by (unfold held in S36; eapply rdbl_transport; [eapply rdbl_sub; [exact LIT | clear - L2; lia | clear; lia] | exact MUX |];
               intros x Hx; left; cbn [outside]; split; [clear - Hx BLL RGC1 RGA1 RGA2 RGA8 RGB L2 ATR; lia|]; split; [clear - Hx S36 L2; lia| exact I]);
         assert (XLIT' : LOCV = 2 -> rdbl bsegs mx (DCTX + 30372) (DCTX + 95940))
           by (intros HL2; eapply rdbl_transport; [exact (XLIT HL2) | exact MUX |];
               intros x Hx; left; cbn [outside]; split; [clear - Hx BDL RGC1 RGA1 RGA2 RGA8 RGB ATR; lia|]; split; [clear - Hx; lia| exact I]);
         (* [comment removed for export] *)
         pose proof FR as FRz; le_blob_seg FRz 32%nat 42%nat; le_blob_seg FRz 30%nat 31%nat; le_blob_seg FRz 22%nat 29%nat; le_blob_seg FRz 0%nat 21%nat;
         sql_blob_last FRF; sql_blob_all SHS;
         eapply LASTK;
         [ exact FRz | exact FRF | exact SHS | eexists; eexists; eexists; exact REP | exact HH3' | split; [exact H5V' | exact H5L] | exact BUF' | exact STK' | exact GAP' | exact SAV'
         | exact MU2 | exact WM2 | assumption | exact LIT' | exact XLIT'
         | clear - L1; lia | clear - L1; lia | unfold held in S5; clear - S5; lia
         | unfold held in S1; unfold held in S2; unfold held in S3; clear - S1 S2 S3; lia
         | unfold held in S1; unfold held in S2; unfold held in S3; clear - S1 S2 S3; lia
         | unfold held in S41; clear - S41; lia
         | (* [comment removed for export] *) unfold held in S67; unfold held in S71; destruct (Z.eq_dec LOCV 2) as [E2|N2];
             [ left; destruct (S71 E2) as (X1 & X2 & _); clear - X1 X2 L2; lia
             | destruct S67 as [(EL1 & EL2)|(EL1 & EL2)]; [left; clear - EL1 EL2 L2; lia | right; clear - N2 EL1 EL2 L2; lia] ]
         | exact AS2 ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF after the run, pc =" UPC
    | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
    end.
Qed.

End CANSEC1.

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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_lkit2 AZ_seq_d_rkit AZ_seq_d_xat AZ_seq_d_ad_at.
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

Section CANSEC1. Context {rc : runConstT}.

Lemma ad_exec6a : forall P OEND LLO LEND LOCV K, sqd_static P OEND LLO LEND LOCV -> 1 <= K <= w_nbSeq P ->
  ad_close8 P OEND LLO LEND LOCV K -> ad_close_sel (fun o => o <= 3) P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK CONT1.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold ad_close_sel. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros m1 c24 c32 c40 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl ofs mtc dpx x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x27 x29 x30 x31 INV LF MF HO HOF HM HXclose1 HSEL.
  unfold ad_close8 in CONT1. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in HK, CONT1.
  pose proof ST as ST0.
  pose proof (sqd_linv_buf _ _ _ _ _ m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as BUFS. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in BUFS.
  pose proof (sqd_copy_facts _ _ _ _ _ m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as (BUF & LIT & STK & CFA). cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in BUF, LIT, STK, CFA.
  apply (sqd_lopen_k _ _ _ _ _ m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sqd_frame sqd_ffr] in FR, FRF. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sqd_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sqd_rg_k _ _ _ _ _ ST); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof MF as MF0. destruct MF as (M1 & M2 & M3 & M4). cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in M1.
  apply (sqd_buf_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros BUFB UBUF RBUF RBUFS GRAN U32 R32 RS32 U64 R64 RS64 TBG.
  sd_static_open ST. unfold held in RGB.
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  cbv beta in HSEL. clear MUL.     (* [comment removed for export] *)
  assert (RG : 4096 <= ole /\ ole + 9 <= 2^47 /\ 4096 <= mtc /\ mtc <= ole /\ B0 <= mtc /\ ole + 8 <= B1 /\ DST <= ole /\ ole + 8 <= OEND /\ B1 < 2^47 /\ mtc = ole - ofs)
    by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HO HOF HM; lia).
  assert (RGM : ole + 16 - ole mod 8 <= B1) by (clear - S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 HO HOF HM; Z.div_mod_to_equations; lia).
  assert (MUL6 : munch [(ole, ole + 8); (FRB - 2224, FRB)] m1 m1) by apply munch_refl.
  assert (KDO : ole + 8 <= FRB \/ FRB + 216 <= ole) by (unfold held in S24; clear - S24 RG RGA5 RGA6 HM HO; lia).
  assert (KDF : ole + 8 <= FF \/ FF + 256 <= ole) by (unfold held in S55; clear - S55 RG HM HO; lia).
  assert (KAO : ole + 8 <= 2147450880 \/ 17594333495296 <= ole) by (unfold held in S69; clear - S69 RG; lia).     (* [comment removed for export] *)
  assert (ZSH2 : rng RNG (KXSHLO + 0x22240 / 8) (shspanZ 0x22240 32)) by exact (shz_lit RNG 0x22240 32 RS32).
  assert (ZSH3 : rng RNG (KXSHLO + 0x22280 / 8) (shspanZ 0x22280 32)) by exact (shz_lit RNG 0x22280 32 RS64).
  assert (CASES : ofs = 0 \/ ofs = 1 \/ ofs = 2 \/ ofs = 3) by (clear - HO HSEL; lia).
  destruct CASES as [C|[C|[C|C]]].
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 0) by (clear - HM; lia). subst mtc.
    destruct (TBG 17488 ltac:(clear; lia)) as (ZT64 & RT64). change (rng RNG 2147468368 1) in RT64. destruct (TBG 17480 ltac:(clear; lia)) as (ZT32 & RT32). change (rng RNG 2147468360 1) in RT32.
    assert (ZSH1 : rng RNG (KXSHLO + ole / 8) (shspanZ ole 8)) by (apply (shz_sub RNG B0 (B1 - B0) ole 8 RBUFS); clear - RG; lia).
    assert (UZ1 : unpZ m1 ole (ole + 8)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) ole (ole + 8) UBUF); unfold KXKEND; clear - RG; lia).
    assert (WN1 : rng RNG ole 8) by (eapply rng_sub; [exact RBUF | clear - RG; lia | clear - RG; lia]).
    (try hold CONT1; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HO; try hold HSEL; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold OKLL; try hold OKOF; try hold OKML; try hold ZT64; try hold ZT32; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO;
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp ole 8; KAApp ole 8; KAUnp 0x22240 32; KAUnp 0x22280 32] [0x94304; 0x94640; 0x94650; 0x9465c; 0x94668; 0x94674; 0x94680; 0x9468c; 0x94698; 0x946a4; 0x946b0; 0x946c0; 0x946cc; 0x946d8; 0x946e4] 400%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 320);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange ole 4096 (2^47 - 9);
     KZWr ole 8;
     KZDisj ole 8 FRB 216;
     KZDisj ole 8 FF 256;
     KZImg 0x22240 0x222cb;
     KZWord (2147450880 + 17488) 1 0;
     KZWord (2147450880 + 17480) 1 0;
     KZWr FRB 216;
     KZWr FF 256;
     KZDisj FF 256 FRB 216]
    [(ole, 8); (FRB, 216); (FF, 256)]
    [(ole, 8); (0x22240, 32); (0x22280, 32); (2147468368, 1); (2147468360, 1); (FRB, 216); (FF, 256)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sqd_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HO; try unfold held in HSEL; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZT64; try unfold held in ZT32; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94304) _ _ _ _) => (eapply (CONT1 _ c24 c32 c40) with (ole := ole) (mlv := mlv); [eapply BUFS; [exact MUL6 | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1; lia | clear - M1 M2 M3; lia] | exact LF0 | exact MF0 | cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; lia | lia | lia | lia])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 1) by (clear - HM; lia). subst mtc.
    destruct (TBG 17488 ltac:(clear; lia)) as (ZT64 & RT64). change (rng RNG 2147468368 1) in RT64. destruct (TBG 17480 ltac:(clear; lia)) as (ZT32 & RT32). change (rng RNG 2147468360 1) in RT32.
    assert (ZSH1 : rng RNG (KXSHLO + (ole - 1) / 8) (shspanZ (ole - 1) 9)) by (apply (shz_sub RNG B0 (B1 - B0) (ole - 1) 9 RBUFS); clear - RG; lia).
    assert (UZ1 : unpZ m1 (ole - 1) ((ole - 1) + 9)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (ole - 1) ((ole - 1) + 9) UBUF); unfold KXKEND; clear - RG; lia).
    assert (WN1 : rng RNG (ole - 1) 9) by (eapply rng_sub; [exact RBUF | clear - RG; lia | clear - RG; lia]).
    (try hold CONT1; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HO; try hold HSEL; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold OKLL; try hold OKOF; try hold OKML; try hold ZT64; try hold ZT32; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO;
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp (ole - 1) 9; KAApp ole 8; KAUnp 0x22240 32; KAUnp 0x22280 32] [0x94304; 0x94640; 0x94650; 0x9465c; 0x94668; 0x94674; 0x94680; 0x9468c; 0x94698; 0x946a4; 0x946b0; 0x946c0; 0x946cc; 0x946d8; 0x946e4] 400%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 320);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange ole 4096 (2^47 - 9);
     KZRange (ole - 1) 4096 (2^47 - 10);
     KZWr ole 8;
     KZDisj ole 8 FRB 216;
     KZDisj ole 8 FF 256;
     KZImg 0x22240 0x222cb;
     KZWord (2147450880 + 17488) 1 0;
     KZWord (2147450880 + 17480) 1 0;
     KZWr FRB 216;
     KZWr FF 256;
     KZDisj FF 256 FRB 216]
    [(ole - 1, 9); (FRB, 216); (FF, 256)]
    [(ole - 1, 9); (0x22240, 32); (0x22280, 32); (2147468368, 1); (2147468360, 1); (FRB, 216); (FF, 256)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sqd_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HO; try unfold held in HSEL; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZT64; try unfold held in ZT32; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94304) _ _ _ _) => (eapply (CONT1 _ c24 c32 c40) with (ole := ole) (mlv := mlv); [eapply BUFS; [exact MUL6 | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1; lia | clear - M1 M2 M3; lia] | exact LF0 | exact MF0 | cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; lia | lia | lia | lia])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 2) by (clear - HM; lia). subst mtc.
    destruct (TBG 17489 ltac:(clear; lia)) as (ZT64 & RT64). change (rng RNG 2147468369 1) in RT64. destruct (TBG 17481 ltac:(clear; lia)) as (ZT32 & RT32). change (rng RNG 2147468361 1) in RT32.
    assert (ZSH1 : rng RNG (KXSHLO + (ole - 2) / 8) (shspanZ (ole - 2) 10)) by (apply (shz_sub RNG B0 (B1 - B0) (ole - 2) 10 RBUFS); clear - RG; lia).
    assert (UZ1 : unpZ m1 (ole - 2) ((ole - 2) + 10)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (ole - 2) ((ole - 2) + 10) UBUF); unfold KXKEND; clear - RG; lia).
    assert (WN1 : rng RNG (ole - 2) 10) by (eapply rng_sub; [exact RBUF | clear - RG; lia | clear - RG; lia]).
    (try hold CONT1; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HO; try hold HSEL; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold OKLL; try hold OKOF; try hold OKML; try hold ZT64; try hold ZT32; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO;
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp (ole - 2) 10; KAApp ole 8; KAUnp 0x22240 32; KAUnp 0x22280 32] [0x94304; 0x94640; 0x94650; 0x9465c; 0x94668; 0x94674; 0x94680; 0x9468c; 0x94698; 0x946a4; 0x946b0; 0x946c0; 0x946cc; 0x946d8; 0x946e4] 400%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 320);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange ole 4096 (2^47 - 9);
     KZRange (ole - 2) 4096 (2^47 - 11);
     KZWr ole 8;
     KZDisj ole 8 FRB 216;
     KZDisj ole 8 FF 256;
     KZImg 0x22240 0x222cb;
     KZWord (2147450880 + 17489) 1 0;
     KZWord (2147450880 + 17481) 1 0;
     KZWr FRB 216;
     KZWr FF 256;
     KZDisj FF 256 FRB 216]
    [(ole - 2, 10); (FRB, 216); (FF, 256)]
    [(ole - 2, 10); (0x22240, 32); (0x22280, 32); (2147468369, 1); (2147468361, 1); (FRB, 216); (FF, 256)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sqd_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HO; try unfold held in HSEL; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZT64; try unfold held in ZT32; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94304) _ _ _ _) => (eapply (CONT1 _ c24 c32 c40) with (ole := ole) (mlv := mlv); [eapply BUFS; [exact MUL6 | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1; lia | clear - M1 M2 M3; lia] | exact LF0 | exact MF0 | cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; lia | lia | lia | lia])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
  - (* [comment removed for export] *) subst ofs. assert (EM : mtc = ole - 3) by (clear - HM; lia). subst mtc.
    destruct (TBG 17489 ltac:(clear; lia)) as (ZT64 & RT64). change (rng RNG 2147468369 1) in RT64. destruct (TBG 17481 ltac:(clear; lia)) as (ZT32 & RT32). change (rng RNG 2147468361 1) in RT32.
    assert (ZSH1 : rng RNG (KXSHLO + (ole - 3) / 8) (shspanZ (ole - 3) 11)) by (apply (shz_sub RNG B0 (B1 - B0) (ole - 3) 11 RBUFS); clear - RG; lia).
    assert (UZ1 : unpZ m1 (ole - 3) ((ole - 3) + 11)) by (apply (unpoisoned_unpZ m1 B0 (B0 + (B1 - B0)) (ole - 3) ((ole - 3) + 11) UBUF); unfold KXKEND; clear - RG; lia).
    assert (WN1 : rng RNG (ole - 3) 11) by (eapply rng_sub; [exact RBUF | clear - RG; lia | clear - RG; lia]).
    (try hold CONT1; try hold BUFS; try hold HK; try hold LF; try hold LF0; try hold ST0; try hold MF0; try hold M3; try hold M4; try hold INV; try hold HO; try hold HSEL; try hold L3; try hold L4; try hold L5; try hold L6; try hold L7; try hold L16F; try hold LJF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold OKLL; try hold OKOF; try hold OKML; try hold ZT64; try hold ZT32; revert S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO; rhold_arith; intros S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RG KDO KDF KAO;
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp (ole - 3) 11; KAApp ole 8; KAUnp 0x22240 32; KAUnp 0x22280 32] [0x94304; 0x94640; 0x94650; 0x9465c; 0x94668; 0x94674; 0x94680; 0x9468c; 0x94698; 0x946a4; 0x946b0; 0x946c0; 0x946cc; 0x946d8; 0x946e4] 400%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 320);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange ole 4096 (2^47 - 9);
     KZRange (ole - 3) 4096 (2^47 - 12);
     KZWr ole 8;
     KZDisj ole 8 FRB 216;
     KZDisj ole 8 FF 256;
     KZImg 0x22240 0x222cb;
     KZWord (2147450880 + 17489) 1 0;
     KZWord (2147450880 + 17481) 1 0;
     KZWr FRB 216;
     KZWr FF 256;
     KZDisj FF 256 FRB 216]
    [(ole - 3, 11); (FRB, 216); (FF, 256)]
    [(ole - 3, 11); (0x22240, 32); (0x22280, 32); (2147468369, 1); (2147468361, 1); (FRB, 216); (FF, 256)];
    runhold_off; try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end);
    try sqd_aclose; kx_mem;
    (try unfold held in CONT1; try unfold held in BUFS; try unfold held in HK; try unfold held in LF; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in M3; try unfold held in M4; try unfold held in INV; try unfold held in HO; try unfold held in HSEL; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in L16F; try unfold held in LJF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ZT64; try unfold held in ZT32; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB);
    lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94304) _ _ _ _) => (eapply (CONT1 _ c24 c32 c40) with (ole := ole) (mlv := mlv); [eapply BUFS; [exact MUL6 | exact WMl | exact KXMI | exact BUF | exact STK | clear - L1 M1; lia | clear - M1 M2 M3; lia] | exact LF0 | exact MF0 | cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; lia | lia | lia | lia])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after the run, pc =" UPC]
      | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
      end).
Qed.

End CANSEC1.
